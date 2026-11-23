module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0058
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfMemISup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.EigCarry

theorem exists_eq_of_mem_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ)
    (E : κ → Submodule ℂ M) (hE : ∀ k, ∀ y ∈ E k, ∀ i, op i y = χ k i • y) (ψ : ι → ℂ) (x : M) (hx0 : x ≠ 0)
    (hx : ∀ i, op i x = ψ i • x) (hmem : x ∈ ⨆ k, E k) : ∃ k, χ k = ψ := by
  first
  | (rename_i h_3 h_4; revert ι κ M h_3 h_4 op χ E hE ψ x hx0 hx hmem; exact @_root_.GlobalTheory.JointEigenSupremum.target)
  | exact @_root_.GlobalTheory.JointEigenSupremum.target
  | exact _root_.GlobalTheory.JointEigenSupremum.target
  | (apply _root_.GlobalTheory.JointEigenSupremum.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenSupremum.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenSupremum.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenSupremum.target ..)

theorem exists_part_eq {ι C H M : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup M] [Module ℂ M] (e : H →ₗ[ℂ] M)
    (op : ι → Module.End ℂ M) (χ : C → ι → ℂ) (N : Submodule ℂ M) (E : C → Submodule ℂ H)
    (hE : ∀ c y, y ∈ E c ↔ e y ∈ N ∧ ∀ i, op i (e y) = χ c i • e y) (S : C → Prop) (c : C) (x : H) (hx : x ∈ E c)
    (h0 : e x ≠ 0) (hs : x ∈ ⨆ (c' : C) (_ : S c'), E c') : ∃ c', S c' ∧ E c' = E c := by
  have hle : (⨆ (c' : C) (_ : S c'), E c') ≤ (⨆ k : {c' // S c'}, (E k.1).map e).comap e := by
    refine iSup₂_le fun c' hc' y hy => ?_
    exact (le_iSup (fun k : {c' // S c'} => (E k.1).map e) ⟨c', hc'⟩) ⟨y, hy, rfl⟩
  obtain ⟨k, hk⟩ := exists_eq_of_mem_iSup op (fun k : {c' // S c'} => χ k.1) (fun k => (E k.1).map e)
    (by rintro k _ ⟨y, hy, rfl⟩; exact ((hE _ y).1 hy).2) (χ c) (e x) h0 ((hE c x).1 hx).2 (hle hs)
  refine ⟨k.1, k.2, ?_⟩
  ext y
  rw [hE, hE]
  exact and_congr_right fun _ => forall_congr' fun q => by rw [congrFun hk q]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ssetF_base {R : RealDat3 D A3 Ks} {F : Face3 D A3} (hC : R.WeakCharacterisation F) : SsetF R.toRealDat A3.A.μ0 = R.SF := by
  have hL := hC.base.lev
  have hQ : R.Q A3.A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
    refine (hL.Q_ram A3.A.μ0 PP).2 (Or.inl hP) ?_
    rw [hL.xi_base]
    intro x hx
    rfl
  ext v
  rw [hC.inert.SF v]
  unfold SsetF
  rw [hQ]
  simp only [Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  exact ⟨fun h => h ▸ rfl, fun h => HeightOneSpectrum.ext h⟩

abbrev RowOp (R : RealDat3 D A3 Ks) : Type :=
  {q : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D (Yc D 0)) //
    Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.SF q.1 q.2.1 q.2.2}

theorem mem_eEc_iff (R : RealDat3 D A3 Ks) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (x : R.HE.H) :
    x ∈ R.EEc c ↔ R.HE.e x ∈ Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) ∧
      ∀ q : RowOp R, heckeOn (R.MY 0) q.1.2.2 (R.HE.e x) = c q.1.1 (dualLab q.1.2.1) • R.HE.e x := by
  unfold RealDat3.EEc partDual partFull
  simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  exact and_congr_right fun _ => ⟨fun h q => h _ _ _ q.2, fun h P d S hS => h ⟨(P, d, S), hS⟩⟩

theorem carries_of_mem (R : RealDat3 D A3 Ks) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (x : R.HE.H)
    (hx : x ∈ R.EEc c) (h0 : R.HE.e x ≠ 0) (hs : x ∈ ⨆ p, R.EEp3 p) : ∃ p, R.Carries p c := by
  have hle : (⨆ p, R.EEp3 p) ≤ ⨆ (c') (_ : ∃ p, R.Carries p c'), R.EEc c' :=
    iSup_le fun p => iSup₂_le fun c' hc' =>
      le_iSup₂_of_le (f := fun c' (_ : ∃ p, R.Carries p c') => R.EEc c') c' ⟨p, hc'⟩ le_rfl
  obtain ⟨c', ⟨p, hp⟩, heq⟩ := exists_part_eq R.HE.e (fun q : RowOp R => heckeOn (R.MY 0) q.1.2.2)
    (fun c q => c q.1.1 (dualLab q.1.2.1)) _ R.EEc (mem_eEc_iff R) (fun c' => ∃ p, R.Carries p c') c x hx h0 (hle hs)
  exact ⟨p, heq ▸ hp.1, (Submodule.map_mono heq.ge).trans hp.2⟩

theorem mem_iSup_eEp3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool) (hP : (R.toCx3 F).PartsE b) (x : R.HE.H)
    (hx : R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)) : x ∈ ⨆ p, R.EEp3 p := by
  have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) x ∈ (R.toCx3 F).EEl b := hx
  rw [← hP.2] at h1
  have h2 : (⨆ p, (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl b) ≤ Tw.sub (twAt D.what₂.embLL A3.A.v0) (⨆ p, R.EEp3 p) := by
    refine iSup_le fun p => inf_le_left.trans fun y hy => ?_
    exact (le_iSup (fun p => R.EEp3 p) p) hy
  exact h2 h1

theorem carries_of_hasEig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c, HasEig R F Y π c → ∃ p, R.Carries p c := by
  intro _ _ _ hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins hHolds _ π c hc
  obtain ⟨hCore, hSF, hEE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hPins.char hHolds.aux.ex
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  unfold HasEig at hc
  rw [hμ, ssetF_base hPins.char] at hc
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT π)
  obtain ⟨U, hU, hU0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨x, hx, hxU⟩ := _root_.GlobalTheory.TypePart.isotE_sub_eigenpart (s := 1) R.toRealDat F.lv2 hCore
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) R.SF hSF Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2 _ _ c hc b U hU
  rw [← hEE] at hx
  refine carries_of_mem R c x hx (hxU ▸ hU0) (mem_iSup_eEp3 R F b (hHolds.prim.sumE b) x ?_)
  rw [hxU]
  exact hU.1

end GlobalTheory.Mem.EigCarry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximal
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open Pointwise

namespace GlobalTheory.TrueGeo.HorizRing

variable {F : Type} [Field F] [NumberField F]

theorem exists_embed (B : Type) [CommRing B] [IsDomain B] [Algebra (𝓞 F) B] [CharZero B] [Algebra.IsAlgebraic ℤ B] :
    ∃ ψ : B →ₐ[𝓞 F] AlgebraicClosure F, Function.Injective ψ := by
  have hinj : Function.Injective (algebraMap (𝓞 F) B) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    change Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker (algebraMap (𝓞 F) B)) = ⊥
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  haveI : Algebra.IsAlgebraic (𝓞 F) B :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ) (RingHom.injective_int _)
  haveI : Module.IsTorsionFree (𝓞 F) B := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree (𝓞 F) (AlgebraicClosure F) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (𝓞 F) F (AlgebraicClosure F)]
    exact (algebraMap F _).injective.comp (IsFractionRing.injective (𝓞 F) F)
  let ψ : B →ₐ[𝓞 F] AlgebraicClosure F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker ψ.toRingHom) h0 hx
    (Algebra.IsAlgebraic.isAlgebraic x) ?_
  change Ideal.comap (algebraMap ℤ B) (RingHom.ker ψ.toRingHom) = ⊥
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem comap_ne_bot {R : Type} [CommRing R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (𝔪 : Ideal R)
    [h : 𝔪.IsMaximal] : 𝔪.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
  intro h0
  letI := Ideal.Quotient.field 𝔪
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : IsJacobsonRing (𝓞 F) := isJacobsonRing_of_isIntegral (R := ℤ)
  haveI : Module.Finite (𝓞 F) (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing _ _
  have hinj : Function.Injective (algebraMap (𝓞 F) (R ⧸ 𝔪)) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsScalarTower.algebraMap_eq (𝓞 F) R (R ⧸ 𝔪), ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, h0]
  exact RingOfIntegers.not_isField F
    ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField _))

theorem exists_valuationSubring {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) (𝔪 : Ideal R) [h : 𝔪.IsMaximal]
    (hk : RingHom.ker ψ ≤ 𝔪) : ∃ A : ValuationSubring K, (∀ x, ψ x ∈ A) ∧ ∀ x, A.valuation (ψ x) < 1 ↔ x ∈ 𝔪 := by
  have hs := ψ.rangeRestrict_surjective
  have hc : (𝔪.map ψ.rangeRestrict).comap ψ.rangeRestrict = 𝔪 := by
    rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left, ← RingHom.ker_eq_comap_bot, RingHom.ker_rangeRestrict]
    exact hk
  have hne : 𝔪.map ψ.rangeRestrict ≠ ⊤ := fun ht => h.ne_top (by rw [← hc, ht, Ideal.comap_top])
  obtain ⟨A, hA, hI⟩ := Ideal.image_subset_nonunits_valuationSubring (A := ψ.range) _ hne
  have hm : ∀ x, ψ x ∈ A := fun x => hA ⟨x, rfl⟩
  refine ⟨A, hm, ?_⟩
  let φ : R →+* A := ψ.codRestrict A hm
  have hle : 𝔪 ≤ (IsLocalRing.maximalIdeal A).comap φ := fun x hx => by
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    exact hI ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩
  have he := h.eq_of_le (Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal A).ne_top) hle
  intro x
  rw [he, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] [CharZero R] (𝔪 : Ideal R), 𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* e.O), (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) R a) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (IsLocalRing.maximalIdeal e.O).comap φ = 𝔪 ∧ φ g ≠ 0 := by
  intro F _ _ R _ _ _ _ _ 𝔪 h𝔪 g hg
  haveI : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans (S := 𝓞 F) inferInstance inferInstance
  obtain ⟨q, hq, hqm, hgq, hc, ha⟩ := GlobalTheory.exists_horizontal_prime_le_of_isMaximal R 𝔪 h𝔪 g hg
  obtain ⟨ψ₀, hψ₀⟩ := @exists_embed F _ _ (R ⧸ q) _ _ _ hc (by convert ha <;> first | rfl | exact Subsingleton.elim _ _)
  let ψ : R →ₐ[𝓞 F] AlgebraicClosure F := ψ₀.comp (Ideal.Quotient.mkₐ (𝓞 F) q)
  have hker : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff ψ₀ hψ₀]
    rfl
  have hψ (a : 𝓞 F) : ψ (algebraMap (𝓞 F) R a) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a) := by
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨A, hA, hAm⟩ := exists_valuationSubring ψ.toRingHom 𝔪 (fun x hx => hqm ((hker x).1 hx))
  let v : HeightOneSpectrum (𝓞 F) := ⟨𝔪.comap (algebraMap (𝓞 F) R), inferInstance, comap_ne_bot 𝔪⟩
  obtain ⟨e⟩ := (ExtConj.main F).1 v
  have hov (x : 𝓞 F) : A.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
    have := hAm (algebraMap (𝓞 F) R x)
    rwa [show ψ.toRingHom (algebraMap (𝓞 F) R x) = _ from hψ x] at this
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over hov (ExtConj.lies_over e)
  have hm (x : R) : σ (ψ x) ∈ e.O := by
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul σ _ A (hA x)
  let φ : R →+* e.O := (σ.toRingEquiv.toRingHom.comp ψ.toRingHom).codRestrict e.O hm
  have hφ (x : R) : (φ x : AlgebraicClosure F) = σ (ψ x) := rfl
  refine ⟨v, e, φ, fun a => ?_, ?_, fun h0 => hgq ?_⟩
  · rw [hφ, hψ, σ.commutes]
  · ext x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hφ, ← hAm]
    have := ReciprocityTheory.Gal.smul_valuation_lt_one_iff σ A (σ (ψ x))
    rw [hσ] at this
    rw [this]
    simp
  · have := hφ g
    rw [h0] at this
    exact (hker g).1 (by simpa using this.symm)

end GlobalTheory.TrueGeo.HorizRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPoint
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

theorem GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ)
    (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X) (h₁ : Reps Eb S₁ φ₁ f₁)
    (h₂ : Reps Eb S₂ φ₂ f₂) : ∃ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ ∧
      CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) := by
  obtain ⟨A, hA, h, hh, hb⟩ := _root_.GlobalTheory.FlagBundle.bears_self F ι m X Y₁ Eb S₁ φ₁ f₁ h₁ Y₁.Fn (ratOf Y₁).pt
  obtain ⟨q, ⟨hq, hqb⟩, -⟩ := h₂.2.2 Y₁.Fn ((ratOf Y₁).pt ≫ f₁) A hA h hh
  have hcq : CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt q := ⟨A, hA, h, hh, hb, hqb⟩
  obtain ⟨B, hB, g, hg, hgb⟩ := _root_.GlobalTheory.FlagBundle.bears_self F ι m X Y₂ Eb S₂ φ₂ f₂ h₂ Y₂.Fn (ratOf Y₂).pt
  obtain ⟨r, ⟨hr, hrb⟩, -⟩ := h₁.2.2 Y₂.Fn ((ratOf Y₂).pt ≫ f₂) B hB g hg
  have hcr : CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt := ⟨B, hr ▸ hB, g, hg, hrb, hgb⟩
  have hsp := _root_.GlobalTheory.FlagBundle.lift_specializes_genericPoint F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ q hq hcq (r (IsLocalRing.closedPoint _))
    (fun K _ p p' hp hpp hc => _root_.GlobalTheory.FlagBundle.conclusion F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ r hr hcr K p p' hp hpp hc)
  have hs : q ≫ Y₂.str = spMap (algebraMap F Y₁.Fn) := by
    have e1 : f₂ ≫ X.str = Y₂.str := h₂.1.inducedModelMorphism_comp_structureMap
    have e2 : f₁ ≫ X.str = Y₁.str := h₁.1.inducedModelMorphism_comp_structureMap
    have e3 : ((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ Y₁.str = spMap (algebraMap F Y₁.Fn) := (ratOf Y₁).pt_s
    calc q ≫ Y₂.str = q ≫ (f₂ ≫ X.str) := congrArg (q ≫ ·) e1.symm
    _ = (q ≫ f₂) ≫ X.str := (Category.assoc _ _ _).symm
    _ = ((ratOf Y₁).pt ≫ f₁) ≫ X.str := congrArg (· ≫ X.str) hq
    _ = (ratOf Y₁).pt ≫ (f₁ ≫ X.str) := Category.assoc _ _ _
    _ = (ratOf Y₁).pt ≫ Y₁.str := congrArg (((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ ·) e2
    _ = _ := e3
  obtain ⟨ψ, rfl⟩ := _root_.GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint F Y₂ Y₁.Fn q hsp hs
  refine ⟨ψ, ?_, hcq⟩
  have key : ∀ (σ : X.Fn →+* Y₁.Fn) (a : X.Fn), (ratOf X).val (spMap σ ≫ (ratOf X).pt) a = σ a := by
    intro σ a
    have hm : a ∈ (ratOf X).O (genericPoint (ratOf X).Z) :=
      (RatModel.O_genericPoint (ratOf X)).symm ▸ Algebra.mem_top
    have h1 := RatModel.val_spMap_comp σ (ratOf X).pt ((ratOf X).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, hm⟩
    have h2 := RatModel.valLoc_eq_val (M := ratOf X) (ratOf X).pt ((ratOf X).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, hm⟩
    exact h1.trans (congrArg σ (h2.trans (RatModel.val_pt (M := ratOf X) a)))
  have H1 : ((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ f₁ = spMap φ₁.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := h₁.1
  have H2 : ((ratOf Y₂).pt : Sp Y₂.Fn ⟶ Y₂.X) ≫ f₂ = spMap φ₂.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := h₂.1
  have e : spMap (ψ.comp φ₂).toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) =
      spMap φ₁.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := by
    have s1 : spMap (ψ.comp φ₂).toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X)
        = spMap ψ.toRingHom ≫ (spMap φ₂.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X)) := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    exact s1.trans ((congrArg (spMap ψ.toRingHom ≫ ·) H2.symm).trans
      ((Category.assoc _ _ _).symm.trans (hq.trans H1)))
  ext a
  have := congrArg (fun y => (ratOf X).val y a) e
  simp only [key] at this
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialFrameMapsBounded
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.UnitPairing

def IsPolyFn (f : ℝ → ℂ) : Prop := ∃ p : Polynomial ℂ, ∀ s : ℝ, f s = p.eval (s : ℂ)

theorem IsPolyFn.const (c : ℂ) : IsPolyFn fun _ => c := ⟨Polynomial.C c, fun s => by simp⟩

theorem IsPolyFn.coe : IsPolyFn fun s => (s : ℂ) := ⟨Polynomial.X, fun s => by simp⟩

theorem IsPolyFn.add {f g : ℝ → ℂ} (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn fun s => f s + g s := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun s => by simp [hp, hq]⟩

theorem IsPolyFn.mul {f g : ℝ → ℂ} (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn fun s => f s * g s := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun s => by simp [hp, hq]⟩

theorem IsPolyFn.sum {ι : Type} (t : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i, IsPolyFn (f i)) :
    IsPolyFn fun s => ∑ i ∈ t, f i s := by
  choose p hp using hf
  exact ⟨∑ i ∈ t, p i, fun s => by simp [hp, Polynomial.eval_finsetSum]⟩

theorem IsPolyFn.prod {ι : Type} (t : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i, IsPolyFn (f i)) :
    IsPolyFn fun s => ∏ i ∈ t, f i s := by
  choose p hp using hf
  exact ⟨∏ i ∈ t, p i, fun s => by simp [hp, Polynomial.eval_prod]⟩

variable {D : D7} {V V' : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel V' S')

theorem ellT_pure (w v : ∀ τ, M.H τ) : ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  simp [ellT]

theorem isPolyFn_ellT (a b : M.Vec) (x : ⨂[ℂ] τ, M.H τ) :
    IsPolyFn fun s => ellT M (fun τ => ((a + (s : ℂ) • b) τ : M.H τ)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, ellT_pure, smul_eq_mul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
      inner_add_left, inner_smul_left, Complex.conj_ofReal]
    exact (IsPolyFn.const _).mul (IsPolyFn.prod _ fun τ => (IsPolyFn.const _).add (IsPolyFn.coe.mul (IsPolyFn.const _)))
  | add x y hx hy =>
    simp only [map_add (f := _)]
    exact hx.add hy

theorem ellT_smul (c : D.what₂.Tau → ℝ) (a : M.Vec) (x : ⨂[ℂ] τ, M.H τ) :
    ellT M (fun τ => (((c τ : ℂ) • a τ : M.sm τ) : M.H τ)) x = (∏ τ, (c τ : ℂ)) * ellT M (fun τ => (a τ : M.H τ)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, ellT_pure, smul_eq_mul, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal,
      Finset.prod_mul_distrib]
    ring
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy, mul_add]

noncomputable def pairing (L : SmT M' →ₗ[ℂ] SmT M) (w : M.Vec) (v : M'.Vec) : ℂ :=
  ellT M (fun τ => (w τ : M.H τ)) (inclT M (L (PiTensorProduct.tprod ℂ v)))

theorem isPolyFn_pairing (L : SmT M' →ₗ[ℂ] SmT M) (a b : M.Vec) (a' b' : M'.Vec) :
    IsPolyFn fun s => pairing M M' L (a + (s : ℂ) • b) (a' + (s : ℂ) • b') := by
  classical
  have h : ∀ s : ℝ, PiTensorProduct.tprod ℂ (a' + (s : ℂ) • b') = ∑ t : Finset D.what₂.Tau,
      (∏ τ, if τ ∈ t then (1 : ℂ) else (s : ℂ)) • PiTensorProduct.tprod ℂ (t.piecewise a' b') := fun s => by
    rw [MultilinearMap.map_add_univ]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hm := (PiTensorProduct.tprod ℂ).map_smul_univ
      (fun τ => if τ ∈ t then (1 : ℂ) else (s : ℂ)) (t.piecewise a' b')
    simp only [RingHom.id_apply] at hm
    rw [← hm]
    congr 1
    funext τ
    by_cases hτ : τ ∈ t <;> simp [Finset.piecewise, hτ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pairing, h, map_sum, map_smul, smul_eq_mul]
  refine IsPolyFn.sum _ fun t => IsPolyFn.mul (IsPolyFn.prod _ fun τ => ?_) (isPolyFn_ellT M a b _)
  by_cases hτ : τ ∈ t
  · simpa [hτ] using IsPolyFn.const 1
  · simpa [hτ] using IsPolyFn.coe

noncomputable def nrm (a : M.Vec) : M.Vec := fun τ => ((‖(a τ : M.H τ)‖⁻¹ : ℝ) : ℂ) • a τ

theorem smul_nrm (a : M.Vec) : (fun τ => ((‖(a τ : M.H τ)‖ : ℝ) : ℂ) • nrm M a τ) = a := by
  funext τ
  by_cases h : a τ = 0
  · simp [nrm, h]
  · have : ‖(a τ : M.H τ)‖ ≠ 0 := by simpa using h
    rw [nrm, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ this, Complex.ofReal_one, one_smul]

theorem norm_nrm (a : M.Vec) (h : (∏ τ, ((‖(a τ : M.H τ)‖ : ℝ) : ℂ)) ≠ 0) (τ : D.what₂.Tau) : ‖(nrm M a τ : M.H τ)‖ = 1 := by
  have h1 : ‖(a τ : M.H τ)‖ ≠ 0 := Complex.ofReal_ne_zero.1 (Finset.prod_ne_zero_iff.1 h τ (Finset.mem_univ τ))
  rw [nrm, Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ h1]

theorem pairing_nrm (L : SmT M' →ₗ[ℂ] SmT M) (w : M.Vec) (v : M'.Vec) :
    pairing M M' L w v = (∏ τ, ((‖(w τ : M.H τ)‖ : ℝ) : ℂ)) * ((∏ τ, ((‖(v τ : M'.H τ)‖ : ℝ) : ℂ)) *
      pairing M M' L (nrm M w) (nrm M' v)) := by
  have h1 : PiTensorProduct.tprod ℂ v = (∏ τ, ((‖(v τ : M'.H τ)‖ : ℝ) : ℂ)) • PiTensorProduct.tprod ℂ (nrm M' v) := by
    have hm := (PiTensorProduct.tprod ℂ).map_smul_univ
      (fun τ => ((‖(v τ : M'.H τ)‖ : ℝ) : ℂ)) (nrm M' v)
    simp only [RingHom.id_apply] at hm
    rw [← hm, smul_nrm]
  have h2 : ∀ x, ellT M (fun τ => (w τ : M.H τ)) x =
      (∏ τ, ((‖(w τ : M.H τ)‖ : ℝ) : ℂ)) * ellT M (fun τ => (nrm M w τ : M.H τ)) x := fun x => by
    rw [← ellT_smul M (fun τ => ‖(w τ : M.H τ)‖)]
    exact congrArg (fun u : M.Vec => ellT M (fun τ => (u τ : M.H τ)) x) (smul_nrm M w).symm
  rw [pairing, pairing, h1, h2, map_smul, map_smul, map_smul, smul_eq_mul]

theorem unit_of_ne {P : Type} [AddCommGroup P] [Module ℂ P] (It : P →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (φ : P) (w : M.Vec) (v : M'.Vec)
    (h : pairing M M' (It φ) w v ≠ 0) :
    (∀ τ, ‖(nrm M w τ : M.H τ)‖ = 1) ∧ (∀ τ, ‖(nrm M' v τ : M'.H τ)‖ = 1) ∧
      ∃ φ', pairing M M' (It φ') (nrm M w) (nrm M' v) = 1 := by
  rw [pairing_nrm] at h
  obtain ⟨h1, h⟩ := mul_ne_zero_iff.1 h
  obtain ⟨h2, h3⟩ := mul_ne_zero_iff.1 h
  refine ⟨norm_nrm M w h1, norm_nrm M' v h2, (pairing M M' (It φ) (nrm M w) (nrm M' v))⁻¹ • φ, ?_⟩
  rw [← inv_mul_cancel₀ h3]
  simp only [pairing, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem exists_pairing_ne {P : Type} [AddCommGroup P] [Module ℂ P] (It : P →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (h : It ≠ 0) :
    ∃ φ w v, pairing M M' (It φ) w v ≠ 0 := by
  have : ∃ φ v, It φ (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra hn
    push Not at hn
    refine h (LinearMap.ext fun φ => ?_)
    exact PiTensorProduct.ext (MultilinearMap.ext fun v => hn φ v)
  obtain ⟨φ, v, hv⟩ := this
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.Mem.PureSep.exists_ellT_ne_zero D V S M _ hv
  exact ⟨φ, w, v, hw⟩

theorem exists_common (U : Type) [AddCommGroup U] [Module ℂ U] (ι : Type) [Finite ι] (f : ι → U → ℂ)
    (h : ∀ i a b, IsPolyFn fun s => f i (a + (s : ℂ) • b)) (h' : ∀ i, ∃ v, f i v ≠ 0) : ∃ v, ∀ i, f i v ≠ 0 :=
  @GlobalTheory.T.exists_common_nonzero_of_polynomial_on_real_lines U _ (Module.complexToReal U) ι _ f h h'

theorem exists_unit_vectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), (∀ k, k + 1 < D.R.m → R.ItY k ≠ 0) → R.ItX ≠ 0 → ∃ (d : ∀ j, (R.MY j).Vec) (dX : R.MX.Vec) (φ : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (φX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank), (∀ j, j < D.R.m → ∀ τ, ‖(d j τ : (R.MY j).H τ)‖ = 1) ∧ (∀ τ, ‖(dX τ : R.MX.H τ)‖ = 1) ∧ (∀ k, k + 1 < D.R.m → ellT (R.MY k) (fun τ => (d k τ : (R.MY k).H τ)) (inclT (R.MY k) (R.ItY k (φ k) (PiTensorProduct.tprod ℂ (d (k + 1))))) = 1) ∧ ellT (R.MY (D.R.m - 1)) (fun τ => (d (D.R.m - 1) τ : (R.MY (D.R.m - 1)).H τ)) (inclT (R.MY (D.R.m - 1)) (R.ItX φX (PiTensorProduct.tprod ℂ dX))) = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hY hX
  classical
  have hm := D.R.two_le_m
  have e1 : ∀ k, ∃ φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank, k + 1 < D.R.m →
      ∃ w v, pairing (R.MY k) (R.MY (k + 1)) (R.ItY k φ) w v ≠ 0 := fun k => by
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨φ, h⟩ := exists_pairing_ne _ _ (R.ItY k) (hY k hk)
      exact ⟨φ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose φ hφ using e1
  obtain ⟨φX, wX, vX, hφX⟩ := exists_pairing_ne _ _ R.ItX hX
  let f : Option (Fin (D.R.m - 1)) → (∀ j, (R.MY j).Vec) × R.MX.Vec → ℂ := fun i u =>
    match i with
    | none => pairing (R.MY (D.R.m - 1)) R.MX (R.ItX φX) (u.1 (D.R.m - 1)) u.2
    | some k => pairing (R.MY k) (R.MY (k + 1)) (R.ItY k (φ k)) (u.1 k) (u.1 (k + 1))
  obtain ⟨u, hu⟩ := exists_common _ _ f (fun i a b => by
      cases i with
      | none => exact isPolyFn_pairing _ _ _ _ _ _ _
      | some k => exact isPolyFn_pairing _ _ _ _ _ _ _) (fun i => by
      cases i with
      | none =>
        refine ⟨(Function.update 0 (D.R.m - 1) wX, vX), ?_⟩
        simpa only [f, Function.update_self] using hφX
      | some k =>
        obtain ⟨w, v, h⟩ := hφ k (by omega)
        refine ⟨(Function.update (Function.update 0 (k : ℕ) w) (k + 1) v, 0), ?_⟩
        simpa only [f, Function.update_self, Function.update_of_ne (Nat.succ_ne_self (k : ℕ)).symm] using h)
  obtain ⟨x1, x2, φX', x3⟩ := unit_of_ne _ _ R.ItX φX _ _ (hu none)
  have e2 : ∀ k, ∃ φ' : PolF D (Yc D (k + 1)).rank (Yc D k).rank, k + 1 < D.R.m →
      (∀ τ, ‖(nrm (R.MY k) (u.1 k) τ : (R.MY k).H τ)‖ = 1) ∧
      pairing (R.MY k) (R.MY (k + 1)) (R.ItY k φ') (nrm _ (u.1 k)) (nrm _ (u.1 (k + 1))) = 1 := fun k => by
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨y1, -, φ', y3⟩ := unit_of_ne _ _ (R.ItY k) (φ k) _ _ (hu (some ⟨k, by omega⟩))
      exact ⟨φ', fun _ => ⟨y1, y3⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose φ' hφ' using e2
  refine ⟨fun j => nrm _ (u.1 j), nrm _ u.2, φ', φX', fun j hj => ?_, x2, fun k hk => (hφ' k hk).2, x3⟩
  by_cases hk : j + 1 < D.R.m
  · exact (hφ' j hk).1
  · obtain rfl : j = D.R.m - 1 := by omega
    exact x1

end GlobalTheory.Mem.UnitPairing
end

