module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1633
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0136
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsRestrictBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem presents_lbPow_toLB {X : Scheme.{0}} [IsIntegral X] (A : CartierDiv X) (l : ℕ) :
    Presents (l • A) (lbPow (toLB A) l) fun j => (j PUnit.unit).1.2 ^ l := by
  refine ⟨isLB_lbPow (isLB_toLB A) l, fun i j h => ?_, fun i x hx => ?_⟩
  · simp only [show (lbPow (toLB A) l).g i j = _ from lbPow_g _ l i j, Units.val_pow_eq_pow_val,
      val_res, map_pow, fnOf_resG, fnOf_toLB_g]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Units.ne_zero _))]
  · exact ((i PUnit.unit).2.2 x ((lbPow_U _ l i).le hx)).nsmul l

theorem secPull_add' {X Y : Scheme.{0}} {L : LB X} (s t : L.Sec) (f : Y ⟶ X) :
    GlobalTheory.secPull (s + t) f = GlobalTheory.secPull s f + GlobalTheory.secPull t f :=
  LB.f_injective (funext fun i => by
    simp only [GlobalTheory.secPull, GlobalTheory.chartSec_f, LB.add_f, map_add (f := _)])

theorem secPull_smul' {X Y : Scheme.{0}} {L : LB X} (c : Γ(X, ⊤)) (s : L.Sec) (f : Y ⟶ X) :
    GlobalTheory.secPull (c • s) f = f.appTop c • GlobalTheory.secPull s f :=
  LB.f_injective (funext fun i => by
    simp only [GlobalTheory.secPull, GlobalTheory.chartSec_f, LB.smul_f, map_mul]
    congr 1
    change ((X.presheaf.map _ ≫ f.appLE _ _ _).hom c) = ((f.appTop ≫ Y.presheaf.map _).hom c)
    rw [Scheme.Hom.map_appLE]
    rfl)

theorem algX_top_eq {X : Scheme.{0}} (p : X ⟶ Sp ℂ) (a : ℂ) :
    algX p ⊤ a = p.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv a) := by
  simp only [algX, RingHom.comp_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem redι_closure_genericPoint {X : Scheme.{0}} (z : X)
    [IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme] :
    redι (Closeds.closure ({z} : Set X)) (genericPoint _) = z := by
  have hcl : closure ({redι (Closeds.closure ({z} : Set X)) (genericPoint _)} : Set X) = closure {z} := by
    rw [← Set.image_singleton, (redι _).isClosedEmbedding.closure_image_eq,
      (genericPoint_spec _).def, Set.image_univ, range_redι]
    rfl
  exact (inseparable_iff_closure_eq.2 hcl).eq

end GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sections_restrict_basis :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p →
      ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l →
        ∃ (r : ℕ) (f : Fin r → X.functionField), (∀ i, f i ∈ (l • A).sections) ∧
          r = (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
            lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X))))) ∧
          ∀ a : Fin r → ℂ, a ≠ 0 → (l • A).GeneratesAt z (∑ i, Cartier.constFn p (a i) * f i) := by
  intro X _ _ p hp A z hA
  haveI hYi : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  obtain ⟨l₁, hl₁⟩ := eventually_atTop.1 (_root_.GlobalTheory.LiftClosed.eventually_exists_secPull_eq X p hp (toLB A) (Closeds.closure ({z} : Set X)) hA)
  refine ⟨l₁, fun l hl => ?_⟩
  letI : Algebra ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) :=
    algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p)
  letI : Module ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
    Module.compHom _ (algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤))
  haveI : IsScalarTower ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤)
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
    ⟨fun a g s => by
      show (algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) a * g) • s =
        algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) a • (g • s)
      rw [mul_smul]⟩
  have hP := presents_lbPow_toLB A l
  have hr : Module.finrank ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec =
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) := by
    rw [← lineBundleGlobalSectionsDim_eq_finrank]
    exact lineBundleGlobalSectionsDim_congr_picardClass (pull_isLB hP.isLB _) (pull_isLB (isLB_toLB _) _)
      (by rw [cls_pull hP.isLB, cls_pull (isLB_toLB _), ← hP.toPic_eq, toPic_apply])
  obtain ⟨v, hv⟩ : ∃ v : Fin (Module.finrank ℂ
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec) →
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec, LinearIndependent ℂ v := by
    by_cases hf : Module.Finite ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec
    · exact ⟨_, (Module.finBasis ℂ _).linearIndependent⟩
    · rw [Module.finrank_of_not_finite hf]
      exact ⟨Fin.elim0, linearIndependent_empty_type⟩
  choose s hs using fun i => hl₁ l hl (v i)
  refine ⟨_, fun i => hP.rat (s i), fun i => hP.rat_mem _, hr, fun a ha => ?_⟩
  have e₁ : ∑ i, Cartier.constFn p (a i) * hP.rat (s i) = hP.rat (∑ i, algX p ⊤ (a i) • s i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, Algebra.smul_def, CartierDiv.algebraMap_top]
    rfl
  have e₂ : GlobalTheory.secPull (∑ i, algX p ⊤ (a i) • s i) (redι (Closeds.closure ({z} : Set X))) = ∑ i, a i • v i := by
    let F : (lbPow (toLB A) l).Sec →+ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
      { toFun := fun t => GlobalTheory.secPull t _
        map_zero' := by
          have := secPull_smul' (0 : Γ(X, ⊤)) (0 : (lbPow (toLB A) l).Sec) (redι (Closeds.closure ({z} : Set X)))
          rwa [zero_smul, map_zero, zero_smul] at this
        map_add' := fun t t' => secPull_add' t t' _ }
    change F _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change GlobalTheory.secPull _ _ = _
    rw [secPull_smul', hs i, algX_top_eq]
    rfl
  have hne : ∑ i, a i • v i ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    exact hi (Fintype.linearIndependent_iff.1 hv a h0 i)
  rw [← e₂] at hne
  have hgen := (sec_ne_zero_iff _).1 hne
  rw [GlobalTheory.nonzeroLocus_secPull] at hgen
  have hgen' : redι (Closeds.closure ({z} : Set X)) (genericPoint _) ∈
      nonzeroLocus (∑ i, algX p ⊤ (a i) • s i) := hgen
  have key : ∀ y : X, y = redι (Closeds.closure ({z} : Set X)) (genericPoint _) →
      y ∈ nonzeroLocus (∑ i, algX p ⊤ (a i) • s i) := fun y hy => hy ▸ hgen'
  have hz := key z (redι_closure_genericPoint z).symm
  rw [e₁]
  exact (hP.generatesAt_rat_iff _).2 hz

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeCmHomomorphismsDefinite
section
set_option autoImplicit false

open NumberField

namespace GlobalTheory.FlatCM.HomLat

theorem exists_selfDual_lieSpan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ Λ : Submodule (𝓞 E) (Fin p → E), Λ.FG ∧ (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) ∧
      (∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
        ∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ = Submodule.span (𝓞 K)
            {w | ∃ c ∈ Λ, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG
  refine ⟨GlobalTheory.FlatCM.HomLat.lat X, _root_.GlobalTheory.FlatCM.HomLat.lat_fg E H hH K ρ σ₁ p X, GlobalTheory.FlatCM.HomLat.intl_mem X,
    fun barE hbar d => ⟨fun hd c hc => _root_.GlobalTheory.FlatCM.GramInt.gram_integral E H hH K ρ σ₁ p X gP gQ hG barE hbar c hc d hd,
      _root_.GlobalTheory.FlatCM.HomLat.mem_lat_of_dual E H hH K ρ σ₁ p X gP gQ hG barE hbar d⟩, ?_⟩
  intro FP FB MP hMP τ hτ τE hτE
  refine le_antisymm (_root_.GlobalTheory.FlatCM.HomLat.LieSpan.eigLat_le_span E H hH K ρ σ₁ p X FP FB MP hMP τ hτ τE hτE) ?_
  refine Submodule.span_le.2 ?_
  rintro w ⟨c, hc, e, he, rfl⟩
  induction hc using Submodule.span_induction generalizing e with
  | mem c hc => exact _root_.GlobalTheory.FlatCM.HomLat.sum_smul_diff_mem_eigLat E H hH K ρ σ₁ p X FP FB MP hMP τ hτ τE hτE c hc e he
  | zero => simp
  | add c d _ _ hc hd =>
    simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
    exact add_mem (hc e he) (hd e he)
  | smul s c _ hc =>
    have h1 : ∑ a, τE ((s • c) a) • MP a e = ∑ a, τE (c a) • MP a ((τ s : K) • e) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 : τE ((s • c) a) = (τ s : K) * τE (c a) := by
        rw [Pi.smul_apply, Algebra.smul_def, map_mul]
        exact congrArg (· * τE (c a)) (hτE s)
      rw [h2, mul_smul, (MP a).map_smul, smul_comm]
    rw [h1]
    exact hc _ (by simpa [algebraMap_smul] using (FP.eigLat (X.A true).t.act τ).smul_mem (τ s) he)

end GlobalTheory.FlatCM.HomLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSettingOfEvenOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitSetting

open GlobalTheory.UU GlobalTheory.LN


set_option maxHeartbeats 1000000 in
theorem exists_setting_of_evenOn (laws : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G) (hE : EvenOn P)
    (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (φ : R →+* V) (hφ : Function.Injective φ)
    (hI : maximalIdeal R ≤ (maximalIdeal V).comap φ) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap φ)).obj G)) (w : _),
      IsCPMap s.P P (spMap φ) (pullback.fst G.hom (spMap φ)) pullback.condition w := by
  obtain ⟨X, _, _, _, Q₀, P₀, hlev, hev⟩ := hE
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback _ G hS
  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  rw [← hP'] at hA'
  obtain ⟨P₀', w₀, H₀⟩ := exists_isLevelCP (maximalIdeal V) 0 P'
  have le : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal V ^ (0 + 1)).comap φ := by
    rw [zero_add, pow_one, pow_one]; exact hI
  let b : R ⧸ maximalIdeal R ^ (0 + 1) →+* V ⧸ maximalIdeal V ^ (0 + 1) := Ideal.quotientMap _ φ le
  have sq : spMap b ≫ thick R (maximalIdeal R) 0 = thick V (maximalIdeal V) 0 ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  obtain ⟨wl, hl⟩ := hlev
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G)
    (H := thickObj R (maximalIdeal R) 0 G)
    (H' := thickObj V (maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := P₀) (N' := P₀') sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R (maximalIdeal R) 0))
    (isGrpPullback_pullback _ (thick V (maximalIdeal V) 0)) H hl H₀
  have := hS.smooth
  have := hS.geomConnected
  have : Smooth (thickObj R (maximalIdeal R) 0 G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have : GeometricallyConnected (thickObj R (maximalIdeal R) 0 G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ hev
  obtain ⟨Q₀', D₀', -, -, -⟩ := ClosedPol.exists_desc_pull pF Q₀ D₀ k₃
  have ev := UniformizationSetting.exists_even_of_desc D₀'
  obtain ⟨wA, hwA⟩ := hA'
  exact ⟨A', ⟨hV, hG', gen', hgen', P', wA, hwA, _, Q₀', P₀', ⟨w₀, H₀⟩, ev⟩, wP, H⟩

end GlobalTheory.Mum.TraitSetting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSmallSectionCountRegimeFromRadiusOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem regime_shiftA : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → P.A.SemiPos D → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Regime (shiftA P u) D := by
  intro hA hHS k _ X _ p D hX P hamp hsemi
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 PUnit fun _ => P.A).1
  have hα := ((hA.arIso k X p D hX).2 PUnit _ Φ hΦ).1 PUnit.unit
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.HSNef.ampleHS_pair hHS k X p D hX P 0 1 0 0 P.A _ (Pair.rep_base k X p P).2.1 hamp hsemi hα
  refine ⟨t₀, fun u hu => ⟨Φ (MvPolynomial.X PUnit.unit ^ (D + 1)) / (D + 1).factorial + ((D : ℝ) + 1) * gdeg P.A D / (D + 1).factorial * u, ((D : ℝ) + 1) * gdeg P.A D / (D + 1).factorial, fun t ht => ?_⟩⟩
  have h := ht₀ (t + u) (by linarith)
  have e : ∀ m : ℕ, (shiftA P u).lc 0 m (Real.exp (t * m)) =
      P.lc ((m : ℤ) * 0 + 0) ((m : ℤ) * 1 + 0) (Real.exp ((t + u) * m)) := by
    intro m
    simp only [Pair.lc, (_root_.GlobalTheory.HSNef.shiftA_props k X p P u).2.1, mul_zero, add_zero, mul_one, ← Real.exp_add]
    congr 4
    push_cast
    ring_nf
  have hfun : (fun m : ℕ => (shiftA P u).lc 0 m (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) =
      fun m : ℕ => P.lc ((m : ℤ) * 0 + 0) ((m : ℤ) * 1 + 0) (Real.exp ((t + u) * m)) / (m : ℝ) ^ (D + 1) :=
    funext fun m => by rw [e]
  rw [hfun]
  convert h using 2
  ring

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectFibrePowerAtSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowChart.Compare

open TopologicalSpace

section Comp

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem gm_self_of_pgen (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w) {Y : Scheme.{0}} (f : Y ⟶ X')
    (y : Y) {j : L.ι} {i : L'.ι} (hj : F (f y) ∈ L.U j) (hi : f y ∈ L'.U i) :
    gm (f ≫ F) y (L.U j ⊓ L.U j) (L.g j j) = 1 := by
  have c := hw Y f y j j i i hj hj hi hi
  rw [gm_self hL' f y hi, inv_one, _root_.mul_one] at c
  exact mul_eq_right.1 c.symm

theorem indep_comp' (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w) (hw' : PGen w')
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j : L.ι) (i i' : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hi : F' (f y) ∈ L'.U i) (hi' : F' (f y) ∈ L'.U i') (hk : f y ∈ L''.U k) :
    gw w (f ≫ F') y j i * gw w' f y i k = gw w (f ≫ F') y j i' * gw w' f y i' k := by
  have a := hw Y (f ≫ F') y j j i i' hj hj hi hi'
  have b := hw' Y f y i i' k k hi hi' hk hk
  rw [gm_self_of_pgen hL' w hw (f ≫ F') y hj hi] at a
  rw [gm_self hL'' f y hk] at b
  rw [a, b]
  generalize gm (f ≫ F') y _ (L'.g i i') = B
  generalize gw w (f ≫ F') y j i' = C
  generalize gw w' f y i' k = D
  rw [_root_.one_mul, inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]

theorem exists_comp' (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL'' : L''.IsLB) :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have glue : ∀ (j : L.ι) (k : L''.ι), ∃ s : Γ(X'', (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i → f y ∈ L''.U k →
        gm f y _ s = gw w (f ≫ F') y j i * gw w' f y i k := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : L'.ι → X''.Opens, ∀ i x, x ∈ W i ↔ F (F' x) ∈ L.U j ∧ F' x ∈ L'.U i ∧ x ∈ L''.U k :=
      ⟨fun i => F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, W i ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull₂.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.2⟩
    have l₁ : ∀ i, W i ≤ F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) := fun i x hx =>
      ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
    have l₂ : ∀ i, W i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k := fun i x hx =>
      ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.2 ((hW i x).1 hx).2.1, ((hW i x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X'', W i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), f y ∈ W i →
        gm f y (W i) (u i) = gw w (f ≫ F') y j i * gw w' f y i k :=
      ⟨fun i => res (l₁ i) (pullU F' _ (w.s (fun _ => j, i))) * res (l₂ i) (w'.s (fun _ => i, k)), fun Y f y i hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ i) hy _).trans (gm_pull f F' y _ (l₁ i hy) _)) (gm_res f y (l₂ i) hy _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
        exact Opens.mem_iSup.2 ⟨i, (hW i x).2 ⟨mem_pull₂.1 hx.1, hi, hx.2⟩⟩) u (fun i i' x hx => by
        have h₁ := (hW i x).1 hx.1
        have h₂ := (hW i' x).1 hx.2
        exact (hu _ (𝟙 X'') x i hx.1).trans ((indep_comp' w w' hw hw' hL' hL'' (𝟙 X'') x j i i' k h₁.1 h₁.2.1
          h₂.2.1 h₁.2.2).trans (hu _ (𝟙 X'') x i' hx.2).symm))
    refine ⟨s, fun Y f y i hj hi hk => ?_⟩
    have hy := (hW i (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ i) hy s).symm.trans ((congrArg (gm f y (W i)) (hs i)).trans (hu Y f y i hy))
  choose s hs using glue
  exact ⟨⟨fun p => s (p.1 PUnit.unit) p.2⟩, fun Y f y j i k hj hi hk => hs j k Y f y i hj hi hk⟩

end Comp

end GlobalTheory.LowChart.Compare

namespace GlobalTheory.LowChart

theorem exists_siegAt_of_siegPB : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : SFam h n ζ) {S S₀ : Scheme.{0}} (g : S ⟶ S₀) (s' : S ⟶ Sp o) (x : S ⟶ F.X), x ≫ F.s = s' → ∀ (c : SiegPre h n ζ s'), SiegPB c F.univ x → ∀ (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (Q : LB (G2 A₀).left) (β : c.A.left ⟶ A₀.left) (β₂ : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ g β → IsSquare β β₂ → LBIso c.P (Q.pull β₂) → ∀ (r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ c.A)), ∃ (v : S ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = s') (β₁ : (GlobalTheory.LowChart.siegAt F v s' hs).A.left ⟶ A₀.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v s' hs).A).left ⟶ (G2 A₀).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v s' hs).A A₀ g β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v s' hs).P (Q.pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v s' hs a).left ≫ β₁ = (∏ i, d i ^ a i).left ≫ β := by
  intro o _ ζ h n F S S₀ g s' x hx c hc A₀ _ _ Q β β₂ hβ hβ₂ hQ r d
  obtain ⟨φ, φ₂, hφ, hφ₂, hP, -⟩ := hc
  have hp : ∀ i, ((d i).left ≫ φ) ≫ F.univ.A.hom = x := fun i => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (d i)]
    exact Category.id_comp _
  obtain ⟨v, hv, hvc⟩ : ∃ v : S ⟶ (powA F r).left, v ≫ (powA F r).hom = x ∧
      ∀ i, v ≫ (coord F i).left = (d i).left ≫ φ :=
    ⟨lift x (fun i => (d i).left ≫ φ) hp, lift_hom _ _ _, fun i => lift_coord _ _ _ i⟩
  have hs : v ≫ toO F r = s' := by
    rw [toO, ← Category.assoc, hv, hx]
  refine ⟨v, hs, ?_⟩
  have hpb : IsGrpPullback (siegAt F v s' hs).A F.univ.A x (Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A) :=
    (Pdiv.PullbackComparison.isGrpPullback _ _).congr hv rfl
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hpb hφ
  haveI := he
  let C := siegAt F v s' hs
  let θ₂ : (G2 C.A).left ⟶ (G2 c.A).left := (CartesianMonoidalCategory.lift (fst C.A C.A ≫ e.hom) (snd C.A C.A ≫ e.hom)).left
  have hθf : θ₂ ≫ (fst c.A c.A).left = (fst C.A C.A).left ≫ e.hom.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_fst, Over.comp_left]
  have hθs : θ₂ ≫ (snd c.A c.A).left = (snd C.A C.A).left ≫ e.hom.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd, Over.comp_left]
  refine ⟨e.hom.left ≫ β, θ₂ ≫ β₂, ((isGrpPullback_of_iso e).comp hβ).congr (Category.id_comp g) rfl,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hβ₂.1, ← Category.assoc, hθf, Category.assoc]
  · rw [Category.assoc, hβ₂.2, ← Category.assoc, hθs, Category.assoc]
  · have hθ₂ : Pdiv.PullbackComparison.pφ₂ (v ≫ (powA F r).hom) F.univ.A = θ₂ ≫ φ₂ :=
      have e1 : (θ₂ ≫ φ₂) ≫ (fst F.univ.A F.univ.A).left =
          (fst C.A C.A).left ≫ Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A := by
        rw [Category.assoc, hφ₂.1, ← Category.assoc, hθf, Category.assoc, heφ]
      have e2 : (θ₂ ≫ φ₂) ≫ (snd F.univ.A F.univ.A).left =
          (snd C.A C.A).left ≫ Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A := by
        rw [Category.assoc, hφ₂.2, ← Category.assoc, hθs, Category.assoc, heφ]
      Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components (G := F.univ.A) _ _
        ((Pdiv.PullbackComparison.pφ₂_fst _ _).trans e1.symm) ((Pdiv.PullbackComparison.pφ₂_snd _ _).trans e2.symm)
    have w1 : LBIso C.P (c.P.pull θ₂) :=
      LBIso.chartPull (chartPullSame F.univ.P (fun _ : PUnit.{1} => Pdiv.PullbackComparison.pφ₂ (v ≫ (powA F r).hom) F.univ.A)
        (fun _ => φ₂) (fun _ => 1) θ₂ (fun _ => hθ₂)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P θ₂ θ₂ rfl) (LBIso.symm hP)
    obtain ⟨w, hw⟩ := hQ
    obtain ⟨w', hw'⟩ := w1
    have pw := (isGen_iff w).1 hw
    have pw' := (isGen_iff w').1 hw'
    obtain ⟨w'', T⟩ := Compare.exists_comp' c.isLB w w' pw pw' C.isLB
    exact ⟨w'', (isGen_iff w'').2 (T.pgen_comp c.isLB pw pw')⟩
  · have hpt : ∀ i, ptAt F v s' hs i ≫ e.hom = d i := fun i =>
      Over.OverMorphism.ext (hφ.1.hom_ext
        (by rw [Over.comp_left, Category.assoc, heφ, ptAt_left, hvc])
        (by rw [Over.comp_left, Category.assoc, Over.w e.hom, Over.w (ptAt F v s' hs i), Over.w (d i)]))
    let ψ : (𝟙_ (Over S) ⟶ C.A) →* (𝟙_ (Over S) ⟶ c.A) :=
      MonoidHom.mk' (· ≫ e.hom) fun a b => MonObj.mul_comp a b e.hom
    intro a
    have key : cAt F v s' hs a ≫ e.hom = ∏ i, d i ^ a i := by
      show ψ (cAt F v s' hs a) = _
      rw [cAt, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow]
      exact congrArg (· ^ a i) (hpt i)
    rw [← Category.assoc, ← Over.comp_left, key]

end GlobalTheory.LowChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothAwayOfQuotientPowEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SmoothAdic

open TensorProduct

theorem exists_smooth_away_of_quotient_pow_equiv : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (O C : Type) [CommRing O] [Algebra R O] [CommRing C] [Algebra R C], Algebra.Smooth R O → Algebra.FiniteType R C → (∀ e : ℕ, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)))) → ∀ q : Ideal C, q.IsPrime → q.comap (algebraMap R C) = maximalIdeal R → ∃ g : C, g ∉ q ∧ Algebra.Smooth R (Localization.Away g) := by
  intro R _ _ _ O C _ _ _ _ hO hC hiso q hq hqm
  have hsm : ∀ e : ℕ, Algebra.Smooth (R ⧸ maximalIdeal R ^ (e + 1))
      (TensorProduct R (R ⧸ maximalIdeal R ^ (e + 1)) C) := by
    intro e
    obtain ⟨φ⟩ := hiso e
    let J := maximalIdeal R ^ (e + 1)
    let φ' : (O ⧸ J.map (algebraMap R O)) ≃ₐ[R ⧸ J] (C ⧸ J.map (algebraMap R C)) :=
      AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective φ
    let ψ : ((R ⧸ J) ⊗[R] O) ≃ₐ[R ⧸ J] ((R ⧸ J) ⊗[R] C) :=
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor O J).symm.trans φ').trans
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C J)
    exact Algebra.Smooth.of_equiv ψ
  haveI := hq
  haveI : Algebra.IsSmoothAt R q :=
    isSmoothAt_of_smooth_quotient_pow R (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top C hsm q hqm
  haveI : Algebra.FinitePresentation R C := Algebra.FinitePresentation.of_finiteType.mp hC
  obtain ⟨g, hg, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R q
  exact ⟨g, hg, hs⟩

end GlobalTheory.SmoothAdic
end

