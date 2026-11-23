module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominatesLinearFormsOnBalancedFormsCm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExtensionConeTransfer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0675
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineInvariantFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_fine_invariant_fan {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {g q : ℕ} {φs : InvFun ℤ}
    (hφ : IsPolFan (id : ℤ → ℤ) g φs) (hq : Module.finrank ℚ E * q ≤ g) (𝒩 : Finset ℕ) (h𝒩 : ∀ N ∈ 𝒩, 1 ≤ N) :
    ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ IsPosFn H φ' ∧
      (∀ (n k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ'.toFun n (fun a b => k * B a b) = k * φ'.toFun n B) ∧
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ' γ →
          (restr (𝓞 E) φs).LinearOn γ ∧ ∀ N ∈ 𝒩, IsFine N γ := by
  classical

  have hpoly : IsPolyFan H.bar q (baseFun (𝓞 E) (fineDen g (𝒩.image (· - 1))) φs (𝒩.image (· - 1))) := by
    intro X _ _ _ _ hX
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.polarisationBaseFunction_properties E H g q φs (𝒩.image (· - 1)) X hφ hq hX
    exact ⟨h1, h2, h3, h4, GlobalTheory.T.exists_finite_rational_polyhedral_cells_upto_aut E H g q φs (𝒩.image (· - 1)) X hφ hq hX (_root_.GlobalTheory.RedTh.hasRedCover E H X)⟩
  have htw : IsTwInv H (baseFun (𝓞 E) (fineDen g (𝒩.image (· - 1))) φs (𝒩.image (· - 1))) := by
    intro σ _ n B
    exact baseFun_twist _ _ _ σ n B
  have hdom : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Dominates H.bar X := by
    intro X _ _ _ _
    exact _root_.GlobalTheory.DomBal.dominates E H X
  obtain ⟨φ', h1, h2, h3, hlin⟩ := _root_.GlobalTheory.PolFan.exists_smooth_refinement E H q _ hdom hpoly htw
  obtain ⟨φ'', k1, k2, k3, k4, k5, kcone⟩ := _root_.GlobalTheory.PolFan.OffDom.exists_extension E H q φ' h1 h2 h3
  refine ⟨φ'', k1, k2, k3, k4, k5, ?_⟩
  intro X _ _ _ _ hX m γ hγ
  have hc : IsCone H.bar φ' γ := kcone X hX m γ hγ
  obtain ⟨hr, hf⟩ := GlobalTheory.T.linearOn_isFine_of_linearOn_polarisationBaseFunction E H g q (fineDen g (𝒩.image (· - 1))) φs (𝒩.image (· - 1)) X
    (fineDen_pos g _) hφ hq hX m γ hc.mem hc.nonneg (hlin X hX m γ hc)
  refine ⟨hr, fun N hN => ?_⟩
  have hfN := hf (N - 1) (Finset.mem_image_of_mem _ hN)
  rwa [Nat.sub_add_cancel (h𝒩 N hN)] at hfN

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisCharacterOfFiniteOrderHeckeCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem galOf_of_orderDvd : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (χ : HChar D.host.E) (n : ℕ), 0 < n → χ.OrderDvd n → (∃ z : D.what₂.LL, IsPrimitiveRoot z n) → ∃ ψ₀, GalOf D χ ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1 := by
  intro hGAR D χ n hn hχ hz
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  have h1 : ∀ x, χ.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) hχ
  have hko : IsOpen (χ.1.ker : Set (Ideles D.host.E)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hn h1
  have hkc : IsClosed (χ.1.ker : Set (Ideles D.host.E)) := Subgroup.isClosed_of_isOpen _ hko
  have hle : art.ker ≤ χ.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc
    · rintro _ ⟨k, rfl⟩
      exact χ.2.2 k
    · rw [GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]
      intro y hy
      have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) :=
        Continuous.units_map _ (continuous_id.prodMk continuous_const)
      have hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) χ.1.ker : Subgroup _) : Set (InfiniteAdeleRing D.host.E)ˣ) :=
        ⟨hkc.preimage hinl, hko.preimage hinl⟩
      exact hcl.connectedComponent_subset (Subgroup.one_mem _) hy
  let e := QuotientGroup.quotientKerEquivOfSurjective art ha.quot.surjective
  let c : Gab D.host.E D.nd.Om →* ℂˣ := (QuotientGroup.lift art.ker χ.1 hle).comp e.symm.toMonoidHom
  have hc : ∀ x, c (art x) = χ.1 x := fun x => by
    show QuotientGroup.lift art.ker χ.1 hle (e.symm (art x)) = χ.1 x
    have : e.symm (art x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
    rw [this]; rfl
  have hcc : Continuous c := by
    rw [ha.quot.isQuotientMap.continuous_iff]
    have : (c ∘ art) = χ.1 := funext hc
    rw [this]; exact χ.2.1
  let r : G D.host.E D.nd.Om →* ℂˣ := c.comp (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om)
  have hrc : Continuous r := hcc.comp continuous_quot_mk
  have hrn : ∀ g, r g ^ n = 1 := fun g => by
    obtain ⟨x, hx⟩ := ha.quot.surjective (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om g)
    show c _ ^ n = 1
    rw [← hx, hc, h1]
  have hro : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow r hrc hn hrn
  obtain ⟨z, hz⟩ := hz
  obtain ⟨ψ, hψ⟩ := GlobalTheory.TwistChoice.exists_char_descent D.what₂.embLL hn hz r hrn
  have hψr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ = r := MonoidHom.ext fun g => Units.ext (hψ g)
  have hker : ψ.ker = r.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    rw [← hψr, MonoidHom.comp_apply]
    constructor
    · intro h; rw [h, map_one]
    · intro h
      apply Units.ext
      apply D.what₂.embLL.injective
      have := congrArg Units.val h
      simpa using this
  refine ⟨ψ, ⟨by rw [hker]; exact hro, art, ha, ?_⟩, fun g => ?_⟩
  · rw [hψr]
    intro x σ hσ
    show χ.1 x = c (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ)
    rw [← hσ, hc]
  · apply Units.ext
    apply D.what₂.embLL.injective
    have := congrArg Units.val (hrn g)
    rw [← hψr] at this
    simpa using this

end GlobalTheory.LevCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodBase
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.LieBase.exists_goodBase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F]
    (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)),
    Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp),
      ∃ (X : Var F) (Eb : Fr (ratOf X) Dw.mult 0) (E' : Fr (ratOf (Φ.C k).Y) Dw.mult Dw.mult)
        (φ : X.Fn →ₐ[F] (Φ.C k).Y.Fn) (f : (Φ.C k).Y.X ⟶ X.X) (Ob : X.X.Opens)
        (Hm : Mat Dw.mult X.Fn → GlobalTheory.CxPts X.str (σ.comp e.toRingHom) → Mat Dw.mult ℂ),
        Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => (Φ.C k).gr x.1 x.2) ∧ IsMetricOn Eb Ob Hm ∧
          IsGood Eb Ob Hm ∧
          ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ),
            antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^
                (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult →
              HasChernIntegral Eb Ob Hm R
                (GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k
  obtain ⟨X, j, f, f₀, Eb, A₀, E', φ, hj, hB, hR, hG⟩ := GlobalTheory.LieBase.exists_base_of_flagCpt E H Dw l Xo c O β Y T F e σ U hσ hU Φ k
  refine ⟨X, Eb, E', φ, f, openPart j, lieGram e U hj f₀ A₀, hR, hG,
    GlobalTheory.LieBase.isMetricOn_lieGram E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hB,
    _root_.GlobalTheory.LieBaseGood.lieGram_isGood E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hB,
    fun la R h => ?_⟩
  convert _root_.GlobalTheory.LieBase.hasChernIntegral_covol_flagDeg E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hB la R h using 3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGridUnitGapFieldContainsValues
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem exists_grid_fieldHas : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) := by
  intro cDep
  have h := StepW.and (_root_.GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt cDep) _root_.GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt
  refine EvG.imp h (fun K _ _ _ _ hK => ?_)
  obtain ⟨S₁, P₁, A, S₂, a1, a2, hh⟩ := hK
  choose M hMf hM using _root_.GlobalTheory.GridField.exists_field_uniform cDep K.s.b
  choose S hSa hS using fun B₀ => _root_.GlobalTheory.finDimSubfield_finGen (M B₀) (hMf B₀)
  refine ⟨fun B f F => S₁ B f F ∪ S B, P₁, A, S₂, ?_, a2, ?_⟩
  · intro B f F z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [a1 B f F z hz, hSa B z hz]
  · intro B f T hO hH hP hA hk hF htriv w hw P x
    have hH' : Has₂ B (S₁ B.toPre f B.KsC) (S₂ B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨h1, h3⟩ := hh B f T hO hH' hP hA hk hF htriv w hw
    obtain ⟨G⟩ := h1 P x
    obtain ⟨G', hG'⟩ := hM B.toPre (w.st x.o.Z) rfl (h3 P x) _ x.m.z.R.toRealDat.toLevCh G
    have hle : M B.toPre ≤ B.fixedCoefficientFieldInComplex := hS B.toPre _ (fun z hz => hH.1 z (Finset.mem_union_right _ hz))
    obtain ⟨j, hj⟩ := _root_.GlobalTheory.exists_embedding_fixedField_of_le_complexImage (w.st x.o.Z) (M B.toPre) hle
    refine ⟨G', GlobalTheory.BigTop.Fun.FieldHas.map j ?_⟩
    rw [hj]; exact hG'

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitCharacterNontrivial
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.CompRamified

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem le_exp_neg_one_of_lt_one' {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le'
  · rw [← WithZero.exp_log hx0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem exists_int_locK_ne (χ : HChar L) (t : SplitPlace L) (ht : χ.TameAt t.w) (hr : ¬ χ.UnrAt t.w) :
    ∃ b : 𝓞 (maximalRealSubfield L), b ∉ t.v.asIdeal ∧ ∃ k : Lˣ,
      (k : L) = ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b : 𝓞 L) : L) ∧ χ.locK t.w k ≠ 1 := by
  classical
  simp only [HChar.UnrAt, not_forall] at hr
  obtain ⟨x, hx, hne⟩ := hr
  have hx' : Valued.v (x : t.w.adicCompletion L) = 1 := hx
  obtain ⟨a, ha⟩ := adic_exists_approx t.w (x : t.w.adicCompletion L) (le_of_eq hx')
  obtain ⟨b, hb⟩ := adic_exists_approx t.v (t.i (a : L)) (t.split_le_one a)
  set c : 𝓞 L := algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b with hcdef
  have hac : a - c ∈ t.w.asIdeal := by
    show a - c ∈ t.ideal
    rw [t.split_mem_ideal]
    have e : t.i ((c : 𝓞 L) : L) =
        algebraMap (𝓞 (maximalRealSubfield L)) (t.v.adicCompletion (maximalRealSubfield L)) b := by
      rw [hcdef, split_coe_algebraMap, AlgHom.commutes]; rfl
    have e2 : ((a - c : 𝓞 L) : L) = (a : L) - (c : L) := by push_cast; rfl
    rw [e2, map_sub, e]
    exact hb
  have hval : ∀ z : 𝓞 L, Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) z) = t.w.valuation L (z : L) := fun z => by
    exact adic_valued_algebraMap (R := 𝓞 L) (K := L) t.w (z : L)
  have hxc : Valued.v ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) < 1 := by
    have e : (x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c =
        ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ a) + algebraMap (𝓞 L) _ (a - c) := by
      rw [map_sub]; ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha ?_)
    rw [hval]
    exact (t.w.valuation_lt_one_iff_mem (a - c)).2 hac
  have hc1 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) = 1 := by
    have e : algebraMap (𝓞 L) (t.w.adicCompletion L) c =
        (x : t.w.adicCompletion L) - ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) := by ring
    rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hx']; exact hxc)]
    exact hx'
  have hbv : b ∉ t.v.asIdeal := by
    intro hm
    have h1 := (t.split_alg_mem b).2 hm
    have h2 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) < 1 := by
      rw [hval]; exact (t.w.valuation_lt_one_iff_mem c).2 h1
    rw [hc1] at h2
    exact lt_irrefl _ h2
  have hc0 : (c : L) ≠ 0 := by
    intro h0
    have : algebraMap (𝓞 L) (t.w.adicCompletion L) c = 0 := by
      show algebraMap L (t.w.adicCompletion L) (c : L) = 0
      rw [h0, map_zero]
    rw [this, map_zero] at hc1
    exact zero_ne_one hc1
  refine ⟨b, hbv, Units.mk0 (c : L) hc0, rfl, ?_⟩
  intro h1
  apply hne
  set y : (t.w.adicCompletion L)ˣ := atFin t.w (Units.mk0 (c : L) hc0) with hydef
  have hy : (y : t.w.adicCompletion L) = algebraMap (𝓞 L) (t.w.adicCompletion L) c := rfl
  have hu : IsUnitAt t.w (y * x⁻¹) := by
    show Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ)) : t.w.adicCompletion L) = 1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, hc1, hx', inv_one, mul_one]
  have hsub : Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : ((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1 =
        -((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) * (x : t.w.adicCompletion L)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hy]
      field_simp
      ring
    rw [e, map_mul, Valuation.map_neg, map_inv₀, hx', inv_one, mul_one]
    exact le_exp_neg_one_of_lt_one' hxc
  have h2 := ht (y * x⁻¹) hu hsub
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [← h2]
  exact h1

end Gen

end GlobalTheory.CompRamified


open GlobalTheory.CompRamified in
theorem GlobalTheory.CompRamified.exists_unit_ne_one : ∀ (D : D7) (cf : CharFrame D) (j : Fin D.R.m) (ξH : HChar D.host.E) (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), ξH.TrivOn D.host.F → (∀ u, ξH.TameAt u) → s.v ∈ qPl D (cf.mu0 j * ξH) → NG.IsCompAt (cf.mu0 j * ξH) s ξ → ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1 := by
  classical
  intro D cf j ξH s ξ htr hta hq hc
  set η := cf.mu0 j * ξH with hη
  have htame : ∀ u, η.TameAt u := fun u x hx h1 => by
    change (cf.mu0 j).loc u x * ξH.loc u x = 1
    rw [(cf.isMu0 j).tame u x hx h1, hta u x hx h1, one_mul]
  have htriv : ∀ k : (D.host.F)ˣ, ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, η.locK P (upF D.host.F k) = 1 := fun k => by
    have h1 := (cf.isMu0 j).triv.1 s.v k
    have h2 := htr.1 s.v k
    rw [GlobalTheory.GalToHecke.resFin_eq] at h1 h2
    rw [hη]
    show ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, ((cf.mu0 j).locK P (upF D.host.F k) * ξH.locK P (upF D.host.F k)) = 1
    rw [Finset.prod_mul_distrib, h1, h2, one_mul]
  obtain ⟨-, w, hw, hram⟩ := hq
  have key : ∃ b : 𝓞 (maximalRealSubfield D.host.E), b ∉ s.v.asIdeal ∧ ∃ k : (D.host.E)ˣ,
      (k : D.host.E) = ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E) ∧
        η.locK w k ≠ 1 := by
    rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw with e | e
    · subst e
      exact exists_int_locK_ne η s (htame _) hram
    · have e2 := (GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s w e).1
      have h := exists_int_locK_ne η (GlobalTheory.TypeTame.conjSP s) (e2 ▸ htame _) (e2 ▸ hram)
      rw [e2] at h
      exact h
  obtain ⟨b, hbv, k, hk, hne⟩ := key
  have hb0 : ((b : maximalRealSubfield D.host.E) : D.host.E) ≠ 0 := by
    intro h0
    apply hbv
    have : (b : maximalRealSubfield D.host.E) = 0 := by exact_mod_cast h0
    have : b = 0 := RingOfIntegers.coe_eq_zero_iff.mp this
    rw [this]; exact s.v.asIdeal.zero_mem
  have hF0 : (b : maximalRealSubfield D.host.E) ≠ 0 := fun h => hb0 (by rw [h]; rfl)
  set f : (D.host.F)ˣ := Units.mk0 (b : maximalRealSubfield D.host.E) hF0 with hfdef
  have hfk : upF D.host.F f = k := by
    apply Units.ext
    rw [hk]
    rfl
  have hsw : η.locK s.w k ≠ 1 := by
    by_cases e : s.w = w
    · rwa [e]
    have hc' : IsConjPl D.host w s.w := (GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw).resolve_left e
    have hab : aboveF (L := D.host.E) D.host.F s.v = {s.w, w} := by
      ext P
      rw [GlobalTheory.GalToHecke.mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hP
        have hov : NG.OverPl P s.v := by rw [← hP]; rfl
        rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s P hov with e' | e'
        · exact Or.inl e'.symm
        · exact Or.inr (GlobalTheory.HeightCounting.TrueConjLabels.eq_of_isConjPl e' hc')
      · rintro (rfl | rfl)
        · exact HeightOneSpectrum.ext s.w_under
        · exact HeightOneSpectrum.ext hw
    have h := htriv f
    rw [hab, Finset.prod_pair e, hfk] at h
    intro h1
    rw [h1, one_mul] at h
    exact hne h
  refine ⟨Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k, ?_, ?_⟩
  · show Valued.v (s.i (k : D.host.E)) = 1
    rw [hk, s.split_val_alg]
    refine le_antisymm (s.v.valuation_le_one b) (not_lt.1 fun h => hbv ((s.v.valuation_lt_one_iff_mem b).1 h))
  · rw [hc.2 k]
    exact hsw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAlgebraicModularFormOfTrivialStabili
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ClassForm

theorem double_coset_unique {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {J : Subgroup (GAf L n)} {g : GAf L n}
    (hg : ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1)
    {γ γ' : GQ L n} {κ κ' : J} (h : (γ : GAf L n) * g * κ = (γ' : GAf L n) * g * κ') : γ = γ' ∧ κ = κ' := by
  have key : g⁻¹ * ((γ' : GAf L n)⁻¹ * γ) * g = (κ' : GAf L n) * (κ : GAf L n)⁻¹ := by
    calc g⁻¹ * ((γ' : GAf L n)⁻¹ * γ) * g
        = g⁻¹ * (γ' : GAf L n)⁻¹ * ((γ : GAf L n) * g * κ) * (κ : GAf L n)⁻¹ := by group
      _ = g⁻¹ * (γ' : GAf L n)⁻¹ * ((γ' : GAf L n) * g * κ') * (κ : GAf L n)⁻¹ := by rw [h]
      _ = (κ' : GAf L n) * (κ : GAf L n)⁻¹ := by group
  have hmem : (γ' : GAf L n)⁻¹ * γ ∈ GQ L n := (GQ L n).mul_mem ((GQ L n).inv_mem γ'.2) γ.2
  have h1 := hg _ hmem (key ▸ J.mul_mem κ'.2 (J.inv_mem κ.2))
  have hγ : (γ : GAf L n) = γ' := by
    rw [inv_mul_eq_one] at h1; exact h1.symm
  refine ⟨Subtype.ext hγ, Subtype.ext ?_⟩
  rw [hγ, mul_assoc, mul_assoc] at h
  exact (mul_left_cancel (mul_left_cancel h))


open Classical in
noncomputable def cosetForm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (w : W) (x : GAf L n) : W :=
  if h : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2 then ((χ h.choose.2 : Kˣ) : K) • ρ h.choose.1 w else 0

theorem cosetForm_apply {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (hg : ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) (w : W) (γ : GQ L n) (κ : J) :
    cosetForm ρ J χ g w ((γ : GAf L n) * g * κ) = ((χ κ : Kˣ) : K) • ρ γ w := by
  have hex : ∃ p : GQ L n × J, (γ : GAf L n) * g * κ = (p.1 : GAf L n) * g * p.2 := ⟨(γ, κ), rfl⟩
  unfold cosetForm
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := double_coset_unique hg hex.choose_spec
  rw [← h1, ← h2]

theorem cosetForm_not {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (w : W) (x : GAf L n) (hx : ¬ ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2) :
    cosetForm ρ J χ g w x = 0 := by
  unfold cosetForm; rw [dite_eq_right hx]

theorem exists_form_of_trivial_stabiliser : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] [Nontrivial W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ) (g : GAf L n), (∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) → ∃ f ∈ NX.TypeSpF L n K ρ J χ, f ≠ 0 := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ g hg
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  refine ⟨cosetForm ρ J χ g w, ⟨fun δ x => ?_, fun μ x => ?_⟩, fun h0 => hw ?_⟩
  · by_cases hx : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2
    · obtain ⟨⟨γ, κ⟩, rfl⟩ := hx
      have e : (δ : GAf L n) * ((γ : GAf L n) * g * κ) = ((δ * γ : GQ L n) : GAf L n) * g * κ := by
        simp [mul_assoc]
      rw [e, cosetForm_apply ρ J χ g hg, cosetForm_apply ρ J χ g hg, map_smul, map_mul, Module.End.mul_apply]
    · have hx' : ¬ ∃ p : GQ L n × J, (δ : GAf L n) * x = (p.1 : GAf L n) * g * p.2 := by
        rintro ⟨⟨γ, κ⟩, hp⟩
        refine hx ⟨(δ⁻¹ * γ, κ), ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] at hp ⊢
        rw [← hp]; group
      rw [cosetForm_not ρ J χ g w _ hx, cosetForm_not ρ J χ g w _ hx', map_zero]
  · by_cases hx : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2
    · obtain ⟨⟨γ, κ⟩, rfl⟩ := hx
      have e : (γ : GAf L n) * g * κ * μ = (γ : GAf L n) * g * ((κ * μ : J) : GAf L n) := by
        simp [mul_assoc]
      rw [e, cosetForm_apply ρ J χ g hg, cosetForm_apply ρ J χ g hg, map_mul, Units.val_mul, mul_comm, mul_smul]
    · have hx' : ¬ ∃ p : GQ L n × J, x * μ = (p.1 : GAf L n) * g * p.2 := by
        rintro ⟨⟨γ, κ⟩, hp⟩
        refine hx ⟨(γ, κ * μ⁻¹), ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hp ⊢
        rw [← mul_assoc, ← hp]; group
      rw [cosetForm_not ρ J χ g w _ hx, cosetForm_not ρ J χ g w _ hx', smul_zero]
  · have := congrFun h0 g
    have e := cosetForm_apply ρ J χ g hg w 1 1
    simp only [OneMemClass.coe_one, one_mul, mul_one, map_one, Units.val_one, one_smul] at e
    rw [e, Module.End.one_apply] at this
    simpa using this

end GlobalTheory.ClassForm
end

