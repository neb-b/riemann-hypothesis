module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenEqOneOfContinuousMulFinitePoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OpenKer

open GlobalTheory.AdelicU Filter Topology

theorem eq_one_on_finite_of_mul : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := by
  intro D T K hK F hF h1 hmul
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin D.sp.cm.sig T.gram
  have hc := continuous_ofFin D.sp.cm.sig T.gram
  have hN : {y | ‖F (ofFin D.sp.cm.sig T.gram y) - 1‖ < 1 / 2} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram) :=
    (isOpen_lt (continuous_norm.comp ((hF.comp hc).sub continuous_const)) continuous_const).mem_nhds
      (by simp [h1])
  have hK' : {y | ofFin D.sp.cm.sig T.gram y ∈ K} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram) :=
    (hK.preimage hc).mem_nhds (by simp [one_mem])
  obtain ⟨W, hW⟩ := NonarchimedeanGroup.is_nonarchimedean _ (inter_mem hN hK')
  refine ⟨W.toSubgroup.comap (projFin D.sp.cm.sig T.gram),
    W.isOpen.preimage (continuous_projFin D.sp.cm.sig T.gram), ?_⟩
  intro k hk hkf
  have hkk : ∀ n : ℕ, ofFin D.sp.cm.sig T.gram (projFin D.sp.cm.sig T.gram (k ^ n)) = k ^ n := fun n => by
    have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig T.gram (k ^ n)
    rwa [mem_finPts.1 (pow_mem hkf n), map_one, one_mul] at h
  have hW' : ∀ n : ℕ, ‖F (k ^ n) - 1‖ < 1 / 2 ∧ k ^ n ∈ K := fun n => by
    have : projFin D.sp.cm.sig T.gram (k ^ n) ∈ W := by
      rw [map_pow]; exact pow_mem (show projFin D.sp.cm.sig T.gram k ∈ W from hk) n
    have h := hW this
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hkk n] at h
    exact h
  have hpow : ∀ n : ℕ, F (k ^ n) = F k ^ n := fun n => by
    induction n with
    | zero => simp [h1]
    | succ n ih =>
      rw [pow_succ, hmul _ (hW' n).2 (pow_mem hkf n) _ (by simpa using (hW' 1).2) hkf, ih, pow_succ]
  exact GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le fun m => by
    rw [← hpow]; exact (hW' m).1.le

end GlobalTheory.OpenKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalHeckeFamilyOnRationalDatumForms
section
namespace RationalFamilyExistence
section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Member.RatFamily

theorem exists_family : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S), R.toLevCh.Is A3.A.μ0 → R.AllPlaces → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) → ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧ GlobalTheory.ExportPin.Reads R cG S Y hL := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R cG S Y hLev hAll hRat
  have hA' : R.Sb = R.Pg := hAll
  obtain ⟨f, hs, hf⟩ := GlobalTheory.ExportPin.Model.exists_reads R cG S Y (fun i P ho k hk => by
    have ho' : Formalism.IndefR.Bridge.SplitOff P (R.Pg : Set (Formalism.L2.DIV.Pl D.host.E)) := by
      rw [← hA']; exact ho
    have hg := (GlobalTheory.splitOff_places R.C.P R.Pg ∅ P hLev.Pg
      (fun v hv => absurd hv (Finset.notMem_empty v)) ho').1
    exact hRat i P ⟨ho, hg⟩ k hk)
  exact ⟨f, hs, hf⟩

end GlobalTheory.CompanionTheory.Member.RatFamily

end
end

end RationalFamilyExistence
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.exists_rational_hecke_family_on_rational_datum_forms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S), R.toLevCh.Is A3.A.μ0 → R.AllPlaces → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) → ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧ GlobalTheory.ExportPin.Reads R cG S Y hL := by
  first | exact @RationalFamilyExistence.GlobalTheory.CompanionTheory.Member.RatFamily.exists_family | exact RationalFamilyExistence.GlobalTheory.CompanionTheory.Member.RatFamily.exists_family | (intros; apply RationalFamilyExistence.GlobalTheory.CompanionTheory.Member.RatFamily.exists_family <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePoint
section
set_option autoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

namespace GlobalTheory.HeckeEx

theorem spMap_epsMul_comp (a b : ℂ) {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) :
    spMap (epsMul a) ≫ spMap (epsMul b) ≫ v = spMap (epsMul (b * a)) ≫ v := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  apply RingHom.ext
  intro x
  ext <;> simp [epsMul] <;> ring

theorem exists_lift_deriv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') {p : ℕ} (hp : p.Prime)
    {y y'' : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P) (hy'' : y'' = F.u j P') (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G))
    (hC : ∀ a ∈ C, a ^ p ^ 2 = 1) (hI : IsHkIsog p y y'' C ψ ψp) :
    ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧
      ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom y),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex i P z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) := by
  subst hy hy''
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := _root_.GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  refine ⟨gam, h, h1, h2, h3, fun w v hvs hd => ?_⟩
  have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ pullback.fst _ _ = (F.ex i P z).left := fun z =>
    pullback.lift_fst _ _ _
  have d0 : IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i P z)) w v := by
    refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
      (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
    · convert ExpChain.isHolTo_ex F i P hP using 2 with z
      exact hfst z
    · convert hd using 2 with z
      exact hfst z
  have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
  have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ ≫ pullback.fst _ _ = (F.ex j P' (h z)).left := fun z => by
    rw [← Category.assoc, hI.2.2.1, h4]
    exact pullback.lift_fst _ _ _
  simp only [e1] at d1
  exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h.toLinearMap w _).1 d1


set_option maxHeartbeats 1000000 in
theorem exists_similitude_tri_of_hkPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → ∃ (gam : (U.X k).Λ →ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (p : ℚ) ^ 2 * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ w : (U.X k').Λ, ∃ v, gam v = (p ^ 2) • w) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ m < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) m = p * ∑ j ∈ Finset.range (Dw.mult τ), A τ m j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (m : Fin (Dw.mult τ)), A τ m m = Formalism.L2.PjFree.toC (t (some ⟨τ, m⟩) : CAt σ) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U _ hU P p i k k' x x' C z t hA hK hH hB
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨Pm, hP, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨Pm', hP', per', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨ψ, ψp, hI, hL, -⟩ := hH
  have hpp : p.Prime := hA.2.2.1
  have hC : ∀ a ∈ C, a ^ p ^ 2 = 1 := fun a ha => GlobalTheory.HkPts.pow_eq_one hA.2.2.2.1 hK ha
  obtain ⟨gam, h, hiso, hh, honto, hder⟩ := exists_lift_deriv F (ik k) (ik k') Pm Pm' per per' hpp hPx
    (hB.1.trans hPx') C ψ ψp hC hI
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hcol : ∀ τ m, h.toLinearMap (Pi.single (e.symm ⟨τ, m⟩) 1) =
      (∑ j, ((p : ℂ) * Formalism.L2.PjFree.toC (cf τ m j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ m
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL τ m
    have d2 := hder (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hv τ m; rw [← hw1] at q; exact q)
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm' per' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ m)
      (z.u τ m)).1 (hPx' ▸ hcf3 τ m)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _ := by
      have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
        apply RingHom.ext
        intro a
        ext <;> simp [epsMul]
      rw [e0]
      first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
    have e3 : spMap (epsMul (p : ℂ)) ≫ z.u τ m = wv ≫ ψ ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0, e1]
      exact Category.id_comp _
    rw [e3] at d3
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm' per'
    show h (Pi.single (e.symm ⟨τ, m⟩) 1) = _
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (smul_smul (p : ℂ) (Formalism.L2.PjFree.toC (cf τ m j)) (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ))
  refine ⟨(φ k').toLinearMap ∘ₗ gam ∘ₗ (φ k).symm.toLinearMap,
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun w => ?_, fun τ i j hji => ?_,
    fun τ m hm v => ?_, fun τ i => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
    push_cast
    ring
  · obtain ⟨a, ha⟩ := honto ((φ k').symm w)
    refine ⟨φ k a, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [ha, map_nsmul, LinearEquiv.apply_symm_apply]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have a1 := hP' (gam v) (e.symm ⟨τ, ⟨m, hm⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range, Finset.mul_sum]
    refine (GlobalTheory.LevelCusp.apply_of_cols e h.toLinearMap
      (fun τ i j => (p : ℂ) * Formalism.L2.PjFree.toC (cf τ i j)) hcol (Pm v) τ ⟨m, hm⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP, Equiv.apply_symm_apply, dite_eq_left ⟨hm, j.2⟩, _root_.mul_assoc]
  · beta_reduce
    rw [dite_eq_left ⟨i.2, i.2⟩]
    exact congrArg _ (hcf1 τ i)

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteClassesRationalIsometriesBoundedDenominatoStatement
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_rational_isometries_bounded_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → ∃ S : Finset (GL (Fin r) E), (∀ s ∈ S, QMatch X X' N s) ∧ ∀ a, QMatch X X' N a → ∃ s ∈ S, ∃ b ∈ X'.Γ, a = b * s := by
  first | exact @GlobalTheory.HeckeEx.QFin.finite_reps | exact GlobalTheory.HeckeEx.QFin.finite_reps | (intros; apply GlobalTheory.HeckeEx.QFin.finite_reps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMaximalCompactCharacterRealPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCharAtPlace

theorem det_eq_detPos_mul_detNeg {k p : ℕ} {κ : Matrix (Fin k) (Fin k) ℂ} (h : IsKMat p κ) :
    κ.det = detPos p κ * detNeg p κ := by
  unfold detPos detNeg
  exact Matrix.twoBlockTriangular_det κ (fun i => i.val < p) (fun i hi j hj => h.2 i j (by tauto))

theorem onb_mul_inv {k p : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) : B * B⁻¹ = 1 := by
  obtain ⟨ε, hε, h1, -⟩ := h
  have hd : (Bᴴ * G * B).det ≠ 0 := by
    rw [h1, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    rcases hε a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e]
  rw [Matrix.det_mul] at hd
  exact Matrix.mul_nonsing_inv _ (Ne.isUnit (right_ne_zero_of_mul hd))

theorem comm_of_onb {k p : ℕ} {G s B κ : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) (hk : IsKMat p κ) :
    s * (B * κ * B⁻¹) = B * κ * B⁻¹ * s := by
  have hB := onb_mul_inv h
  have hB' : B⁻¹ * B = 1 := mul_eq_one_comm.1 hB
  obtain ⟨ε, hε, -, h2⟩ := h
  have hs : s = B * diagonal (fun a => (ε a : ℂ)) * B⁻¹ := by
    rw [← h2, Matrix.mul_assoc, hB, Matrix.mul_one]
  have hc : diagonal (fun a => (ε a : ℂ)) * κ = κ * diagonal (fun a => (ε a : ℂ)) := by
    ext i j
    rw [diagonal_mul, mul_diagonal]
    by_cases hij : (i.val < p ↔ j.val < p)
    · have e : ε i = ε j := by
        rcases hε i with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hε j with ⟨b1, b2⟩ | ⟨b1, b2⟩
        · rw [a1, b1]
        · exact absurd (hij.1 a2) (by omega)
        · exact absurd (hij.2 b2) (by omega)
        · rw [a1, b1]
      rw [e, mul_comm]
    · rw [hk.2 i j hij, mul_zero, zero_mul]
  rw [hs]
  calc B * diagonal (fun a => (ε a : ℂ)) * B⁻¹ * (B * κ * B⁻¹)
        = B * (diagonal (fun a => (ε a : ℂ)) * (B⁻¹ * B) * κ) * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = B * (κ * (B⁻¹ * B) * diagonal (fun a => (ε a : ℂ))) * B⁻¹ := by
        rw [hB', Matrix.mul_one, Matrix.mul_one, hc]
    _ = B * κ * B⁻¹ * (B * diagonal (fun a => (ε a : ℂ)) * B⁻¹) := by simp only [Matrix.mul_assoc]

theorem alg {A B C E : ℂ} (cS cT : ℤ) (pS qS pT qT : ℕ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hE : E ≠ 0) :
    ((A * B) ^ cT)⁻¹ * (C * E) ^ cS * (C ^ pS * E ^ qS * (A ^ pT)⁻¹ * (B ^ qT)⁻¹) =
      A ^ (-cT - (pT : ℤ) - (qT : ℤ) + (qT : ℤ)) * B ^ (-cT - (pT : ℤ) - (qT : ℤ) + (pT : ℤ)) *
        (C ^ (cS + (pS : ℤ)) * E ^ (cS + (qS : ℤ))) := by
  have e1 : -cT - (pT : ℤ) - (qT : ℤ) + (qT : ℤ) = -cT - (pT : ℤ) := by ring
  have e2 : -cT - (pT : ℤ) - (qT : ℤ) + (pT : ℤ) = -cT - (qT : ℤ) := by ring
  rw [e1, e2, mul_zpow, mul_zpow, zpow_add₀ hC, zpow_add₀ hE, zpow_sub₀ hA, zpow_sub₀ hB, _root_.zpow_neg, _root_.zpow_neg]
  simp only [zpow_natCast]
  have := zpow_ne_zero cT hA
  have := zpow_ne_zero cT hB
  have := pow_ne_zero pT hA
  have := pow_ne_zero qT hB
  field_simp

end GlobalTheory.VacCharAtPlace


open GlobalTheory.VacCharAtPlace in
theorem GlobalTheory.VacCharAtPlace.vacuum_char_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ τ : D.what₂.Tau, ∃ mS mT : ℤ, ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∀ κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ g h, IsAtTau θ S τ (BS τ * κS * (BS τ)⁻¹) g → IsAtTau θ T τ (BT τ * κT * (BT τ)⁻¹) h → om (g, h) f = (detPos (pS τ) κS ^ (mS + (T.rank - pT τ : ℕ)) * detNeg (pS τ) κS ^ (mS + pT τ) * (detPos (pT τ) κT ^ (mT + pS τ) * detNeg (pT τ) κT ^ (mT + (S.rank - pS τ : ℕ)))) • f := by
  intro D ψ θ S T χS χT om hW hθ τ
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  obtain ⟨aS, haS⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χS S.rank τ hθ hW.hecS hW.resS
  obtain ⟨aT, haT⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χT T.rank τ hθ hW.hecT hW.resT
  obtain ⟨cS, hcS⟩ := GlobalTheory.CompactFockAction.exp_twist_int hθ S hW.resS e3 haS (e2 τ)
  obtain ⟨cT, hcT⟩ := GlobalTheory.CompactFockAction.exp_twist_int hθ T hW.resT e3 haT (e2 τ)
  refine ⟨-cT - T.rank, cS, ?_⟩
  intro sS BS sT BT pS pT hpS hpT hCS hCT hOS hOT f hf hv κS κT hkS hkT g h hg hh
  classical
  have cg : ∀ ρ, compAt θ ρ (Formalism.L2.Theta.mt S g) = if ρ = τ then BS τ * κS * (BS τ)⁻¹ else 1 := fun ρ => by
    split_ifs with e
    · subst e; exact hg.2.1
    · exact hg.2.2 ρ e
  have ch : ∀ ρ, compAt θ ρ (Formalism.L2.Theta.mt T h) = if ρ = τ then BT τ * κT * (BT τ)⁻¹ else 1 := fun ρ => by
    split_ifs with e
    · subst e; exact hh.2.1
    · exact hh.2.2 ρ e
  have ginv : ∀ ρ, compAt θ ρ (Formalism.L2.Theta.mt S g⁻¹) = (compAt θ ρ (Formalism.L2.Theta.mt S g))⁻¹ := fun ρ =>
    (Matrix.inv_eq_right_inv (GlobalTheory.WeilVacMove.compAt_mt_mul_inv θ ρ S g)).symm
  have commS : ∀ ρ, sS ρ * compAt θ ρ (Formalism.L2.Theta.mt S g) = compAt θ ρ (Formalism.L2.Theta.mt S g) * sS ρ := fun ρ => by
    rw [cg]; split_ifs with e
    · subst e; exact comm_of_onb (hOS ρ) hkS
    · rw [Matrix.mul_one, Matrix.one_mul]
  have commT : ∀ ρ, sT ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * sT ρ := fun ρ => by
    rw [ch]; split_ifs with e
    · subst e; exact comm_of_onb (hOT ρ) hkT
    · rw [Matrix.mul_one, Matrix.one_mul]
  have dS : ∀ ρ, (compAt θ ρ (Formalism.L2.Theta.mt S g)).det = if ρ = τ then κS.det else 1 := fun ρ => by
    rw [cg]; split_ifs
    · exact Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (onb_mul_inv (hOS τ)))) κS
    · exact Matrix.det_one
  have dT : ∀ ρ, (compAt θ ρ (Formalism.L2.Theta.mt T h)).det = if ρ = τ then κT.det else 1 := fun ρ => by
    rw [ch]; split_ifs
    · exact Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (onb_mul_inv (hOT τ)))) κT
    · exact Matrix.det_one
  have nS : ‖κS.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hkS.1)
  have nT : ‖κT.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hkT.1)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq κS.det two_pos
  obtain ⟨v, hv'⟩ := IsAlgClosed.exists_pow_nat_eq κT.det two_pos
  have hw1 : ‖w‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [← norm_pow, hw, nS])
  have hv1 : ‖v‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [← norm_pow, hv', nT])
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.CompactFockAction.exists_root_at hθ S hg.1 τ w hw1 (by rw [dS, if_pos rfl, hw])
    (fun ρ e => by rw [dS, if_neg e])
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.CompactFockAction.exists_root_at hθ T hh.1 τ v hv1 (by rw [dT, if_pos rfl, hv'])
    (fun ρ e => by rw [dT, if_neg e])
  rw [_root_.GlobalTheory.WeilVacChar.vacuum_character D ψ hW.std S T θ hθ χS χT om η ⟨e1, e4, e3, e2⟩ hW sS sT hCS hCT g hg.1 h hh.1 commS commT x y hx hy
    f hf hv]
  congr 1
  have vx : (((χT * (η ^ T.rank)⁻¹) x : Circle) : ℂ) = κS.det ^ cT := by
    rw [hxv _ (aT - T.rank / 2) (2 * cT) (GlobalTheory.VacuumCharacter.hasInfExp_twist haT (e2 τ) T.rank)
      (by push_cast; rw [hcT]), _root_.zpow_mul, ← hw]
    norm_cast
  have vy : (((χS * (η ^ S.rank)⁻¹) y : Circle) : ℂ) = κT.det ^ cS := by
    rw [hyv _ (aS - S.rank / 2) (2 * cS) (GlobalTheory.VacuumCharacter.hasInfExp_twist haS (e2 τ) S.rank)
      (by push_cast; rw [hcS]), _root_.zpow_mul, ← hv']
    norm_cast
  have hP : ∏ ρ, GlobalTheory.WeilParts.detPlus (sS ρ) (sT ρ) (compAt θ ρ (Formalism.L2.Theta.mt S g⁻¹))
      (compAt θ ρ (Formalism.L2.Theta.mt T h)) =
      GlobalTheory.WeilParts.detPlus (sS τ) (sT τ) (BS τ * κS * (BS τ)⁻¹)⁻¹ (BT τ * κT * (BT τ)⁻¹) := by
    rw [Finset.prod_eq_single τ (fun ρ _ e => by
        rw [ginv, cg, ch, if_neg e, if_neg e, inv_one]; exact GlobalTheory.CompactFockAction.detPlus_one_one _ _)
      (by simp), ginv, cg, ch, if_pos rfl, if_pos rfl]
  have d0S := det_eq_detPos_mul_detNeg hkS
  have d0T := det_eq_detPos_mul_detNeg hkT
  have nz : ∀ {a b c : ℂ}, ‖c‖ = 1 → c = a * b → a ≠ 0 ∧ b ≠ 0 := fun {a b c} hc e => by
    have : c ≠ 0 := fun h0 => by simp [h0] at hc
    rw [e] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  obtain ⟨hA, hB⟩ := nz nS d0S
  obtain ⟨hC, hE⟩ := nz nT d0T
  rw [Circle.coe_mul, Circle.coe_inv, vx, vy, hP,
    _root_.GlobalTheory.PlusDetONB.detPlus_onb (gramAt D S τ) (sS τ) (BS τ) κS (gramAt D T τ) (sT τ) (BT τ) κT (pS τ) (pT τ) (hpS τ) (hpT τ)
      (hOS τ) (hOT τ) hkS hkT, d0S, d0T,
    show (-cT - (T.rank : ℤ)) = -cT - (pT τ : ℤ) - ((T.rank - pT τ : ℕ) : ℤ) by push_cast [hpT τ]; ring]
  exact alg cS cT (pS τ) (S.rank - pS τ) (pT τ) (T.rank - pT τ) hA hB hC hE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedPointDescendsFiniteSubextension
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem exists_finite_factor {F R K L : Type} [Field F] [CommRing R] [Field K] [Field L] [Algebra F R]
    [Algebra F K] [Algebra F L] [Algebra.FiniteType F R] (φ : K →ₐ[F] L) (hφ : φ.toRingHom.IsIntegral)
    (ψ : R →ₐ[F] L) :
    ∃ (M : Type) (_ : Field M) (_ : Algebra F M) (i : K →ₐ[F] M) (j : M →ₐ[F] L) (χ : R →ₐ[F] M),
      j.comp i = φ ∧ i.toRingHom.Finite ∧ j.comp χ = ψ := by
  classical
  letI : Algebra K L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F R).out
  let M : IntermediateField K L := IntermediateField.adjoin K ((s.image ψ : Finset L) : Set L)
  haveI hM : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => hφ x
  have hmem : ∀ r : R, ψ r ∈ M.toSubalgebra.restrictScalars F := by
    intro r
    have hr : r ∈ Algebra.adjoin F (s : Set R) := hs ▸ Algebra.mem_top
    have : Algebra.adjoin F (s : Set R) ≤ (M.toSubalgebra.restrictScalars F).comap ψ := by
      refine Algebra.adjoin_le fun x hx => ?_
      exact IntermediateField.subset_adjoin K _ (by simpa using ⟨x, hx, rfl⟩)
    exact this hr
  refine ⟨M, inferInstance, inferInstance, IsScalarTower.toAlgHom F K M, M.val.restrictScalars F,
    ψ.codRestrict (M.toSubalgebra.restrictScalars F) hmem, ?_, ?_, ?_⟩
  · ext a; rfl
  · exact RingHom.finite_algebraMap.2 hM
  · ext a; rfl

theorem frPt_descends_finite :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (z : FrPt Xo c L), φ.toRingHom.IsIntegral → ∃ (M : Type) (_ : Field M) (_ : Algebra c.F M) (i : K →ₐ[c.F] M) (j : M →ₐ[c.F] L) (z₁ : FrPt Xo c M), j.comp i = φ ∧ i.toRingHom.Finite ∧ FrMap j z₁ z := by
  intro E _ _ _ H Dw l Xo c K L _ _ _ _ φ z hφ
  obtain ⟨p, ψ, u, hu⟩ := GlobalTheory.FlagTan.fromTest_of_isLocalRing z
  haveI : Algebra.FiniteType c.F p.R := inferInstance
  obtain ⟨M, _, _, i, j, χ, h1, h2, h3⟩ := exists_finite_factor φ hφ ψ
  obtain ⟨z₁, hz⟩ := GlobalTheory.FlagTan.exists_frMap χ u
  exact ⟨M, inferInstance, inferInstance, i, j, z₁, h1, h2,
    GlobalTheory.FlagTan.frMap_of_comp hz hu fun a => DFunLike.congr_fun h3 a⟩

end GlobalTheory.HkIntegral
end
end

