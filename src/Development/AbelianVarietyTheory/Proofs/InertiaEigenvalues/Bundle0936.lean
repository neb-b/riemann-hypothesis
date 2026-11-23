module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0862
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralFormsEqSpanDedekindCoefRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0931
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0928
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleThetaValuedMapMemThetaData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrilinearThetaFormReferenceTupleInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteFormReadingInjectiveLatticeIntegralForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceExp

section Alg

variable {R K E V A : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [Field E] [Algebra R E]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup A] [Module ℂ A]

theorem span_one_tmul (hE : Function.Injective (algebraMap R E)) {I : Type} (v : I → V)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    Submodule.span E (Set.range fun i => ((1 : E) ⊗ₜ[R] v i : E ⊗[R] V)) = ⊤ := by
  have key : ∀ f : V, ((1 : E) ⊗ₜ[R] f : E ⊗[R] V) ∈
      Submodule.span E (Set.range fun i => ((1 : E) ⊗ₜ[R] v i : E ⊗[R] V)) := fun f => by
    have hf : f ∈ Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) a
      have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
      have hqK : algebraMap R K q ≠ 0 := by simpa using hq0
      have hqE : algebraMap R E q ≠ 0 := fun h => hq0 (hE (h.trans (map_zero _).symm))
      rw [← Submodule.smul_mem_iff _ hqE, algebraMap_smul, ← TensorProduct.tmul_smul, ← algebraMap_smul K q, smul_smul,
        mul_div_cancel₀ _ hqK, algebraMap_smul, TensorProduct.tmul_smul, ← algebraMap_smul E p]
      exact Submodule.smul_mem _ _ hx
  refine Submodule.eq_top_iff'.2 fun y => ?_
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => exact add_mem hx hy
  | tmul a f =>
    have : (a ⊗ₜ[R] f : E ⊗[R] V) = a • ((1 : E) ⊗ₜ[R] f) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (key f)

theorem injective_of_indep {W : Type} [AddCommGroup W] [Module E W] {ε : E →+* ℂ} (φ : W →ₛₗ[ε] A) {I : Type} (u : I → W)
    (hu : Submodule.span E (Set.range u) = ⊤) (hi : LinearIndependent ℂ fun i => φ (u i)) : Function.Injective φ := by
  refine (injective_iff_map_eq_zero φ).2 fun y hy => ?_
  have hy' : y ∈ Submodule.span E (Set.range u) := hu ▸ Submodule.mem_top
  obtain ⟨l, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hy'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum] at hy
  simp only [map_smulₛₗ] at hy
  have h := linearIndependent_iff'.1 hi _ _ hy
  refine Finset.sum_eq_zero fun i hi' => ?_
  have : l i = 0 := ε.injective ((h i hi').trans (map_zero _).symm)
  simp only [this, zero_smul]

theorem indep_fieldRange {e : K →+* ℂ} (g : V →ₛₗ[e] A) (hg : Function.Injective g) {I : Type} {v : I → V}
    (hv : LinearIndependent K v) : LinearIndependent e.fieldRange fun i => g (v i) := by
  refine linearIndependent_iff'.2 fun t c h i hi => ?_
  choose d hd using fun i => RingHom.mem_fieldRange.1 (c i).2
  have h1 : g (∑ i ∈ t, d i • v i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hd]
    rfl
  have h2 := linearIndependent_iff'.1 hv _ _ (hg (h1.trans (map_zero _).symm)) i hi
  exact Subtype.ext ((hd i).symm.trans (by rw [h2, map_zero]; rfl))

end Alg

theorem rdE_injective_lattice : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)) (T : CellTie hρ D.nexp rd) (ε : KE c w →+* ℂ) (hε : Extends ρ ε), TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  Function.Injective (rdE T hε) ∧ ∀ F : Amb D j, F ∈ (ρ.B (c.twI w) j (c.sd w)).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia ρ ε) ↔ ∃ y ∈ latT c w (j.1 + 1), rdE T hε y = F := by
  intro D c w ρ hρ j rd T ε hε hok hr
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent (FractionRing (D.ntw.Ok (c.twI w) (c.k' w)))
      (D.nexp.MtLat (c.twI w) (j.1 + 1) (c.sd w) (c.k' w) (c.Q w) (chr c w) :
        Set (D.nexp.MtV (c.twI w) (j.1 + 1) (c.sd w) (c.k' w) (c.Q w) (chr c w)))
    rw [D.nexp.MtLat_span] at hspan
    have hE : Function.Injective (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w)) := fun a b h =>
      ρ.eOk_injective (c.twI w) (c.sd w) (c.k' w) (by rw [← hε.apply, ← hε.apply, h])
    refine injective_of_indep (rdE T hε) _ (span_one_tmul (K := FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) hE
      (Subtype.val : s → _) (by rw [Subtype.range_coe]; exact hspan)) ?_
    have h1 := indep_fieldRange _ (T.rdV_inj _ _ _ hok) hli
    have h2 := _root_.GlobalTheory.PlaceIndep.linearIndependent_complex D _ _ _ (hρ.base (c.twI w) j (c.sd w)) _ _ _ _ (hρ.isCoefRing_k (c.twI w) (c.sd w) (c.k' w))
      (ρ.ek (c.twI w) (c.sd w) (c.k' w)).fieldRange (by rintro _ ⟨x, rfl⟩; exact ⟨_, rfl⟩) _ _
      (fun a h => ((Base.mem_mtLat _ _ _ _).1 ((T.rdV_mem hok).1 (hs a.2))).2 h) h1
    simpa only [rdE_tmul, map_one, one_smul] using h2
  · obtain ⟨hg, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ _ ρ hρ (c.twI w) j (c.sd w) _ _ _ hok
    have hle : (ρ.eOk (c.twI w) (c.sd w) (c.k' w)).range ≤ ringOf ε := by
      rintro _ ⟨x, rfl⟩
      refine ⟨algebraMap _ _ x, ?_⟩
      rw [← hε.apply, IsScalarTower.algebraMap_apply (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w) (KE c w)]
      rfl
    have hbc := _root_.GlobalTheory.FormsBaseChange.mtLat_eq_span D _ _ _ (hρ.base (c.twI w) j (c.sd w)) _ hg hadm _ _ _ _ _
      (ρ.eOk_injective (c.twI w) (c.sd w) (c.k' w)) (hρ.isCoefRing_k (c.twI w) (c.sd w) (c.k' w))
      (levLam_mem_eOk hr T hok) _ hle
    have hsm : ∀ (a : c.Oe w) (y : Tgt c w (j.1 + 1)), rdE T hε (a • y) = ε (algebraMap _ _ a) • rdE T hε y := fun a y => by
      rw [← algebraMap_smul (KE c w) a y, map_smulₛₗ]
    intro F
    rw [hε.twVia_eq, hbc]
    constructor
    · intro hF
      induction hF using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := (T.mtLat_iff _ _ _ hok x).1 hx
        refine ⟨_, Submodule.subset_span ⟨f, hf, rfl⟩, ?_⟩
        rw [TensorProduct.mk_apply, rdE_tmul, map_one, one_smul]
      | zero => exact ⟨0, zero_mem _, map_zero _⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', hx, rfl⟩ := hx
        obtain ⟨y', hy, rfl⟩ := hy
        exact ⟨x' + y', add_mem hx hy, map_add _ _ _⟩
      | smul a x _ hx =>
        obtain ⟨x', hx, rfl⟩ := hx
        obtain ⟨_, a, rfl⟩ := a
        exact ⟨a • x', Submodule.smul_mem _ _ hx, hsm a x'⟩
    · rintro ⟨y, hy, rfl⟩
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        rw [TensorProduct.mk_apply, rdE_tmul, map_one, one_smul]
        exact Submodule.subset_span ((T.rdV_mem hok).1 hf)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [hsm]
        exact Submodule.smul_mem _ (⟨ε (algebraMap _ _ a), a, rfl⟩ : ringOf ε) hx

end GlobalTheory.PlaceExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleDatumFormReadsThetaLiftInnerProducStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_datumForm_reads_thetaLift_innerProducts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1)) (y : D.what₂.Mj (i.1 + 1)) (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)), (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x → inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.RefTheta.phi0 Y i) Fm ⟨X.φ y, X.φ_mem y⟩ := by
  first | exact @GlobalTheory.RefThetaRead.main | exact GlobalTheory.RefThetaRead.main | (intros; apply GlobalTheory.RefThetaRead.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleFormsSmoothAdmissibleUnitaryModuleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_forms_smoothAdmissibleUnitaryModule : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), GlobalTheory.RefTheta.IsCanonR Y i rfl X := by
  first | exact @GlobalTheory.RefRowMod.main | exact GlobalTheory.RefRowMod.main | (intros; apply GlobalTheory.RefRowMod.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleThetaValuedMapMemThetaDataStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_thetaValued_map_mem_thetaData : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO R.ψ (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) (φ v)) → φ ∈ GlobalTheory.RefTheta.Om Ad i hc := by
  first | exact @GlobalTheory.RefTheta.mem_Om_of_theta | exact GlobalTheory.RefTheta.mem_Om_of_theta | (intros; apply GlobalTheory.RefTheta.mem_Om_of_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleWeilDatumCharactersStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_weilDatum_characters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).1 (R.C.mu0 i) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) := by
  first | exact @GlobalTheory.RefTupleChars.ref_chars | exact GlobalTheory.RefTupleChars.ref_chars | (intros; apply GlobalTheory.RefTupleChars.ref_chars <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIsotypicInjective
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.LiftRef.UpInjRows

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev

theorem thetaT_inj_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → ∀ (i : Fin D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = 0 → y = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i σ y hy h0
  exact GlobalTheory.T.adjoint_concrete_theta_injective_reference_tuple D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH i σ y hy (GlobalTheory.T.adjointTheta_kills_referenceTuple D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH i σ y hy h0)

end GlobalTheory.LiftRef.UpInjRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrilinearThetaFormReferenceTupleInvariantStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trilinearThetaForm_referenceTuple_invariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), φ ∈ GlobalTheory.RefTheta.Om Ad i hc → ∀ (Fm Fm' : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y y' : ↥X.C), (Fm' : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = NG.rt D.host.E D.R.nV h Fm → (y' : X.A) = X.ρ g y → GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.ThetaTri.valAct1 (GlobalTheory.RefTheta.omStd Ad i (GlobalTheory.RefTheta.t0 Y)) (h, g) φ) Fm' y' = GlobalTheory.RefTheta.lamV Ad i hc φ Fm y := by
  first | exact @GlobalTheory.RefTheta.lamV_inv | exact GlobalTheory.RefTheta.lamV_inv | (intros; apply GlobalTheory.RefTheta.lamV_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProductStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
                       (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ ∧
          GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x =
            ((H x * (GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) := by
  first | (exact @GlobalTheory.RSEulerId.thetaZ_eq_mul_eulD) | (exact GlobalTheory.RSEulerId.thetaZ_eq_mul_eulD) | (intros; apply GlobalTheory.RSEulerId.thetaZ_eq_mul_eulD  <;> assumption)
end

