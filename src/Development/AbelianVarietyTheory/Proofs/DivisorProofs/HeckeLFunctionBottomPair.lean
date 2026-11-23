module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelOfIsBlockLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeVacuumReading
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorOrthogonalTranslateFinitePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865

@[expose] public section

noncomputable section

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

namespace GlobalTheory.NormRatio

section General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem reads_sum {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ι : Type}
    (s : Finset ι) (G : ι → Formalism.MainNotions.TaylorLogMetric.VC D a d → ℂ) (f : ι → WO S T → ℂ) (h : ∀ i ∈ s, Reads ψ θ hS hT cc δ r (G i) (f i)) :
    Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem ip_eq (ν : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) : ip S T ν 𝓕 f g = GlobalTheory.Ker.ipO ν 𝓕 f g := rfl

theorem ip_sum_left (hψ : IsStdChar D ψ (-1)) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) : ip S T ν 𝓕 (∑ i ∈ s, f i) g = ∑ i ∈ s, ip S T ν 𝓕 (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact GlobalTheory.Size.ipO_add_left hψ hν.1 hν.2.1 (hf i) ((GlobalTheory.FinWeilO.thetaSub ψ S T).sum_mem fun j _ => hf j) hg

theorem ip_sum_right (hψ : IsStdChar D ψ (-1)) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) : ip S T ν 𝓕 g (∑ i ∈ s, f i) = ∑ i ∈ s, ip S T ν 𝓕 g (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact GlobalTheory.Size.ipO_add_right hψ hν.1 hν.2.1 hg (hf i) ((GlobalTheory.FinWeilO.thetaSub ψ S T).sum_mem fun j _ => hf j)

theorem isSphOff_sum {LS : Lat S} {LT : Lat T} {Sf : Finset (FinPl D)} {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ)
    (hf : ∀ i ∈ s, IsSphOff ψ S T LS LT Sf (f i)) : IsSphOff ψ S T LS LT Sf (∑ i ∈ s, f i) := by
  have key : ∀ u, (∀ i ∈ s, heisO ψ S T u (f i) = f i) → heisO ψ S T u (∑ i ∈ s, f i) = ∑ i ∈ s, f i := by
    intro u hu
    funext w
    simp only [heisO, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => congrFun (hu i hi) w
  exact ⟨fun u hu => key _ fun i hi => (hf i hi).1 u hu, fun e he u hu hh => key _ fun i hi => (hf i hi).2 e he u hu hh⟩

theorem isSphOff_pure (hθ : IsInfFam θ) {LS : Lat S} {LT : Lat T} {Sf : Finset (FinPl D)} {f : WO S T → ℂ}
    (hf : IsSphOff ψ S T LS LT Sf f) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (p : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsSphOff ψ S T LS LT Sf (pureTensorO ψ θ S T sS sT BS BT f p) :=
  ⟨fun u hu => by
    rw [← GlobalTheory.VacPairSchur.pT_heisO hθ sS BS sT BT f (GlobalTheory.FockLatVac.infPart_latO_any (nsmul_mem hu 2)), hf.1 u hu],
   fun e he u hu hh => by
    rw [← GlobalTheory.VacPairSchur.pT_heisO hθ sS BS sT BT f (GlobalTheory.FockLatVac.infPart_latO_any hu), hf.2 e he u hu hh]⟩

theorem volQ_eq_mass (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (h1 : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V) (h2 : Function.Injective ι) (h3 : ι.range = GfC V)
    (h4 : ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n)
    (h5 : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K) (h6 : ∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ intG D n)
    (h7 : Links.IsMeasDef V K μ 𝓕) : (volQ V μ : ℂ) = mass D n := by
  have h := (_root_.GlobalTheory.NormDictClassSum.integral_eq_classSum V n ι (intG D n) K μ 𝓕 h1 h2 h3 h4 h5 h6 h7 (fun _ => 1)
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩).2.2
  simpa [GlobalTheory.AutomorphicL2Unitary.descend, volQ, mass] using h

theorem openOff_conj {V : HSp D} {L : Lat V} {Sf : Finset (FinPl D)} {a g b : GA D V} (ha : a ∈ openOff V L ∅)
    (hg : g ∈ openOff V L Sf) (hb : b ∈ openOff V L ∅) : a⁻¹ * g * b ∈ openOff V L Sf := fun v hv => by
  rw [map_mul, map_mul, map_inv]
  exact mul_mem (mul_mem (inv_mem (ha v (Finset.notMem_empty v))) (hg v hv)) (hb v (Finset.notMem_empty v))

end General

section Translates

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : GlobalTheory.Core.Rk.IP.WRep S T}
  {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} {G : Type} [Group G] (ι : G →* GA D S)

theorem om_mul_one (om : GlobalTheory.Core.Rk.IP.WRep S T) (g g' : GA D S) (f : WO S T → ℂ) :
    om (g * g', 1) f = om (g, 1) (om (g', 1) f) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem coef_sum (hom : IsWeilDatumO ψ S T χS χT om) (hν : IsCovolOne (ratL T S) ν 𝓕) {φ : WO S T → ℂ}
    (hφ : IsThetaFunO ψ S T φ) (R : Finset G) (x : G) :
    ip S T ν 𝓕 (om (ι x, 1) (∑ y ∈ R, om (ι y, 1) φ)) (∑ y ∈ R, om (ι y, 1) φ) =
      ∑ y ∈ R, ∑ y' ∈ R, ip S T ν 𝓕 (om (ι (y'⁻¹ * x * y), 1) φ) φ := by
  have hth : ∀ g : GA D S, IsThetaFunO ψ S T (om (g, 1) φ) := fun g => hom.om_pres _ _ hφ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [← om_mul_one]
  rw [ip_sum_left hom.std hν R _ (fun _ => hth _) ((GlobalTheory.FinWeilO.thetaSub _ _ _).sum_mem fun j _ => hth _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ip_sum_right hom.std hν R _ (fun _ => hth _) (hth _)]
  refine Finset.sum_congr rfl fun y' _ => ?_
  have e : ι x * ι y = ι y' * ι (y'⁻¹ * x * y) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [ip_eq, ip_eq, ← GlobalTheory.Size.ipO_om hom hν.1 hν.2.1 (hth (ι (y'⁻¹ * x * y))) hφ (ι y', 1), ← om_mul_one, e]

theorem norm_sum (hom : IsWeilDatumO ψ S T χS χT om) (hν : IsCovolOne (ratL T S) ν 𝓕) {φ : WO S T → ℂ}
    (hφ : IsThetaFunO ψ S T φ) (R : Finset G)
    (h : ∀ y ∈ R, ∀ y' ∈ R, y' ≠ y → ip S T ν 𝓕 (om (ι (y'⁻¹ * y), 1) φ) φ = 0) :
    ip S T ν 𝓕 (∑ y ∈ R, om (ι y, 1) φ) (∑ y ∈ R, om (ι y, 1) φ) = (R.card : ℂ) * ip S T ν 𝓕 φ φ := by
  have h1 := coef_sum ι hom hν hφ R 1
  rw [map_one, Prod.mk_one_one, map_one, Module.End.one_apply] at h1
  have h2 : ∀ y ∈ R, ∑ y' ∈ R, ip S T ν 𝓕 (om (ι (y'⁻¹ * 1 * y), 1) φ) φ = ip S T ν 𝓕 φ φ := by
    intro y hy
    rw [Finset.sum_eq_single_of_mem y hy]
    · rw [mul_one, inv_mul_cancel, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]
    · intro y' hy' hne
      rw [mul_one]
      exact h y hy y' hy' hne
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]

theorem mem_of_conj_mem {H : Subgroup G} {a b x : G} (ha : a ∈ H) (hb : b ∈ H) (h : a⁻¹ * x * b ∈ H) : x ∈ H := by
  have := mul_mem (mul_mem ha h) (inv_mem hb)
  rwa [show a * (a⁻¹ * x * b) * b⁻¹ = x by group] at this

theorem openOff_conj_hom {L : Lat S} {Sf : Finset (FinPl D)} {a g b : G} (ha : ι a ∈ openOff S L ∅)
    (hg : ι g ∈ openOff S L Sf) (hb : ι b ∈ openOff S L ∅) : ι (a⁻¹ * g * b) ∈ openOff S L Sf := by
  rw [map_mul, map_mul, map_inv]
  exact openOff_conj ha hg hb

theorem norm_arith {A B C : ℂ} {c N e : ℕ} {n v L : ℝ} (h1 : A = (c : ℂ) * B) (h2 : B = ((N : ℂ) ^ e)⁻¹ * C) (h3 : C = n)
    (h4 : n = v) (h5 : (c : ℝ) * ((N : ℝ) ^ e)⁻¹ = L) : A = (L : ℂ) * (v : ℂ) := by
  rw [h1, h2, h3, h4, ← h5]
  push_cast
  ring

end Translates

section Exact

variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}

theorem congOne_one (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : CongOne D 𝔪 (1 : Formalism.MainNotions.StandardLatticesGL3.GA D N) := fun i j => by simp

theorem vac_eq_of_reads (h : IsExact P X r) {G : Formalism.MainNotions.TaylorLogMetric.VC D P.a P.d → ℂ} {f : WO X.A X.B → ℂ} (hF : P.F = G)
    (h1 : Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r G f) : X.vac = f := by
  subst hF
  exact h.read.unique h1

theorem vac_eq_sum (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} (hm : 𝔪 ≠ ⊥) {o : ℕ}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hF : P.F = ∑ y ∈ R, P.W.Om y 1 (cosetVec P 𝔪 o)) {φ : WO X.A X.B → ℂ}
    (hφ : Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ) : X.vac = ∑ y ∈ R, X.om (X.ιA y, 1) φ := by
  have h1 : ∀ y, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (P.W.Om y 1 (cosetVec P 𝔪 o)) (X.om (X.ιA y, 1) φ) := fun y => by
    have := h.reads_om hI y 1 (GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT P hm o) hφ
    rwa [X.ιB.map_one] at this
  exact vac_eq_of_reads h hF (reads_sum R (fun y => P.W.Om y 1 (cosetVec P 𝔪 o)) (fun y => X.om (X.ιA y, 1) φ) fun y _ => h1 y)

theorem exists_reads_coset (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} (hm : 𝔪 ≠ ⊥) (o : ℕ) :
    ∃ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ :=
  _root_.GlobalTheory.NormExact.ReadEx.exists_reads X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r h.setup (cosetVec P 𝔪 o) (GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT P hm o)

theorem exists_reads_vacuum (h : IsExact P X r) : ∃ f₀, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ :=
  _root_.GlobalTheory.NormExact.ReadEx.exists_reads X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r h.setup P.e0
    (GlobalTheory.NormSum.VacMove.vac_TT (GlobalTheory.InducedType.induced_type D).1 P.crv P.vac.1)

theorem mem_openOff (h : IsExact P X r) {x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} (hx : x ∈ intG D P.a) (Sf : Finset (FinPl D)) :
    X.ιA x ∈ openOff X.A (stdLat X.A) Sf := fun v _ =>
  (_root_.GlobalTheory.NormRatio.selfDual_and_mem_intG_iff X.A P.a (X.ιA x) x h.std.frame.gramA X.rkA (h.std.ptA x)).2.1 hx v (Finset.notMem_empty v)

theorem norm_transl (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hR : ∀ y ∈ R, y ∈ intG D P.a)
    (hRu : ∀ k ∈ intG D P.a, ∃! y, y ∈ R ∧ CongOne D 𝔪 (y⁻¹ * k)) {φ : WO X.A X.B → ℂ} (hφ : IsThetaFunO X.ψ X.A X.B φ)
    {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (horth : ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
      ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0) :
    ip X.A X.B ν 𝓕 (∑ y ∈ R, X.om (X.ιA y, 1) φ) (∑ y ∈ R, X.om (X.ιA y, 1) φ) = (R.card : ℂ) * ip X.A X.B ν 𝓕 φ φ := by
  refine norm_sum X.ιA h.weil hν hφ R fun y hy y' hy' hne =>
    horth _ (mem_openOff h (mul_mem (inv_mem (hR y' hy')) (hR y hy)) Sf) fun hc => hne ?_
  have h1 : CongOne D 𝔪 (y⁻¹ * y) := by rw [inv_mul_cancel]; exact congOne_one 𝔪 _
  exact (hRu y (hR y hy)).unique ⟨hy', hc.2⟩ ⟨hy, h1⟩

theorem supp_transl (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hR : ∀ y ∈ R, y ∈ intG D P.a) {φ : WO X.A X.B → ℂ} (hφ : IsThetaFunO X.ψ X.A X.B φ)
    {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (horth : ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
      ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0) {x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} (hx : x ∉ intG D P.a)
    (hx' : X.ιA x ∈ openOff X.A (stdLat X.A) Sf) :
    ip X.A X.B ν 𝓕 (X.om (X.ιA x, 1) (∑ y ∈ R, X.om (X.ιA y, 1) φ)) (∑ y ∈ R, X.om (X.ιA y, 1) φ) = 0 := by
  refine (coef_sum X.ιA h.weil hν hφ R x).trans ?_
  refine Finset.sum_eq_zero fun y hy => Finset.sum_eq_zero fun y' hy' => horth _ ?_ fun hc => hx ?_
  · exact openOff_conj_hom X.ιA (mem_openOff h (hR y' hy') ∅) hx' (mem_openOff h (hR y hy) ∅)
  · exact mem_of_conj_mem (hR y' hy') (hR y hy) hc.1

theorem finite_data (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} {o : ℕ}
    (hm : GoodMod D 𝔪 Sf) (hstd : IsStdDatum P 𝔪 o) (ho : o + P.a ≤ P.d) :
    (∃ LB : Lat X.B, IsSelfDualC X.B LB ∧ IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf X.vac) ∧
    ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
      ip X.A X.B ν 𝓕 X.vac X.vac = (locNorm D 𝔪 P.a (P.d - P.a) : ℂ) * (vacNorm D ⊤ δ t0 P.a P.d : ℂ) ∧
      ∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ip X.A X.B ν 𝓕 (X.om (X.ιA x, 1) X.vac) X.vac = 0 := by
  obtain ⟨R, hR, hRu, hF⟩ := hstd
  refine (exists_reads_coset h hm.1 o).elim fun φ hφ => ?_
  refine (exists_reads_vacuum h).elim fun f₀ hf₀ => ?_
  refine (_root_.GlobalTheory.NormRatio.vacLat_of_reads X.ψ X.θ X.A X.B X.rkA X.rkB δ r h.setup).elim fun LB ⟨hLB, hz, hsph⟩ => ?_
  have hs₀ := hsph P.e0 P.vac.1 f₀ hf₀
  have hsd := (_root_.GlobalTheory.NormRatio.selfDual_and_mem_intG_iff X.A P.a (X.ιA 1) 1 h.std.frame.gramA X.rkA (h.std.ptA 1)).1
  have hv := vac_eq_sum hI h hm.1 hF hφ
  have hsφ := _root_.GlobalTheory.NormRatio.SphCoset.sph P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ
  have hs := isSphOff_sum R (fun y => X.om (X.ιA y, 1) φ) fun y hy =>
    _root_.GlobalTheory.SphMove.isSphOff_om X.ψ X.A X.B X.χA X.χB X.om h.weil _ _ hsd hLB Sf _ (mem_openOff h (hR y hy) Sf) φ hφ.1 hsφ
  refine ⟨⟨LB, hLB, by rw [hv]; exact hs⟩, fun ν 𝓕 hν => ?_⟩
  have horth := _root_.GlobalTheory.NormRatio.ip_om_cosetVec_eq_zero P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ ho ν 𝓕 hν
  refine ⟨?_, fun x hx hx' => by rw [hv]; exact supp_transl h hR hφ.1 hν horth hx hx'⟩
  have h3 := GlobalTheory.T.thetaCosetIndicatorReading_normSq_eq_absNorm_inv_mul_vacuum P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ ν 𝓕 hν
  have h4 := GlobalTheory.T.thetaLineReading_adelicNorm_eq_torusMeanSquare X.ψ X.θ X.A X.B X.rkA X.rkB δ r h.setup LB hLB hz P.e0 P.vac.1 f₀ hf₀ hs₀ ν 𝓕 hν
  have h5 := _root_.GlobalTheory.NormRatio.card_transversal_mul D 𝔪 hm.1 hm.2.1 P.a (P.d - P.a) R hR hRu
  rw [Nat.add_sub_cancel' P.a_le] at h5
  have h6 := norm_transl h hR hRu hφ.1 hν horth
  exact norm_arith (by rw [hv]; exact h6) h3 h4 P.vac.2.2.1 h5

end Exact

section Fock

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}

theorem var_injective (X : Data P) : Function.Injective X.var := by
  rintro ⟨τ, i, j⟩ ⟨τ', i', j'⟩ e
  simp only [Data.var, Prod.mk.injEq, Fin.cast_inj] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

theorem ip_fock (hX : IsDict P X) {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (T : Tup D P.a P.d P.n) : ip X.A X.B ν 𝓕 (X.fock T) (X.fock T) =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) * ip X.A X.B ν 𝓕 X.vac X.vac := by
  have h := GlobalTheory.FockIsometry.ipO_pureTensorO D X.ψ X.θ X.A X.B hX.2.weil.std hX.2.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => X.A.rank) (fun _ => X.B.rank) (fun _ => le_rfl) (fun _ => le_rfl)
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB)
    (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramA) (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramB) X.vac hX.2.vac_theta hX.2.vac_fock
    ν 𝓕 hν (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T))
  have e : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T)) =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) := by
    rw [GlobalTheory.FockCoefReal.fockIp_eq_fock, GlobalTheory.LowRowFock.fock_rename_inj (var_injective X), ← GlobalTheory.FockCoefReal.fockIp_eq_fock]
  have e2 : ip X.A X.B ν 𝓕 X.vac X.vac = (nrm2 ν 𝓕 X.vac : ℂ) := GlobalTheory.Size.ipO_self ν 𝓕 X.vac
  exact h.trans (by rw [e, e2])

theorem ip_fock_zero (hX : IsDict P X) {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (T : Tup D P.a P.d P.n) {g : GA D X.A} (hg : g ∈ GfC X.A) (h0 : ip X.A X.B ν 𝓕 (X.om (g, 1) X.vac) X.vac = 0) :
    ip X.A X.B ν 𝓕 (X.om (g, 1) (X.fock T)) (X.fock T) = 0 := by
  refine (GlobalTheory.FockCoefSplit.pair_eq_inf D X.ψ X.θ X.A X.B X.χA X.χB X.om hX.2.weil hX.2.inf (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (fun _ => X.A.rank) (fun _ => X.B.rank)
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB)
    (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramA) (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramB) ν 𝓕 hν 1 (one_mem _) 1 (one_mem _)
    (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T))).elim fun c hc => ?_
  have h1 := hc X.vac (X.om (g, 1) X.vac) hX.2.vac_theta (hX.2.weil.om_pres _ _ hX.2.vac_theta) hX.2.vac_fock
    fun τ => GlobalTheory.FockCoefSplit.fockVac_om_fin hX.2.weil hX.2.inf hg (one_mem _) τ _ hX.2.vac_theta (hX.2.vac_fock τ)
  have h2 := GlobalTheory.FockCoefSplit.om_fin_pureTensorO hX.2.weil hX.2.inf (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) hg
    (one_mem (GfC X.B)) hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))
  rw [GlobalTheory.VacPairSchur.thetaIP_eq_ipO, GlobalTheory.VacPairSchur.thetaIP_eq_ipO, ← h2, Prod.mk_one_one, X.om.map_one,
    Module.End.one_apply, ← ip_eq, ← ip_eq, h0, mul_zero] at h1
  exact h1

theorem isFockVec_fock (hX : IsDict P X) (T : Tup D P.a P.d P.n) :
    IsFockVec X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (X.fock T) :=
  GlobalTheory.FockSph.isFockVec_pureTensorO (sS := fun _ => 1) (sT := fun _ => 1) hX.2.weil.std hX.2.inf
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB) (fun _ => 1) (fun _ => 1)
    hX.2.vac_theta hX.2.vac_fock _

theorem wcoef_fock (hX : IsDict P X) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)) (T : Tup D P.a P.d P.n)
    (g : GA D X.A) {k : GA D X.A} (hk : k ∈ GinfC X.A) : wcoef X.om ν 𝓕 (X.fock T) (X.fock T) (g * k) =
      ip X.A X.B ν 𝓕 (X.om (g, 1) (X.fock T)) (X.fock T) := by
  rw [wcoef, om_mul_one, _root_.GlobalTheory.NormDict.om_real_fock_eq P X hX hX.2.infB k hk T]

end Fock

section Norm

variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}

def normFactor (D : D7) (δ t0 : ℂ) (a d : ℕ) (n : D.what₂.Tau → ℕ) : ℂ :=
  (normConst D ⊤ δ a n : ℂ) * mass D d * mass D a * fockSum D a d n * (vacNorm D ⊤ δ t0 a d : ℂ) /
    GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a d (((d - a : ℕ) : ℂ) / 2)

theorem collect {c I mB mA L dS d0 F l v : ℂ} (h : I * l * d0 = dS) (h0 : d0 ≠ 0) (hS : dS ≠ 0) :
    c * I * (mB * mA * (L / dS) * (F * (l * v))) = c * mB * mA * F * v / d0 * L := by
  rw [← h] at hS ⊢
  have h1 : I ≠ 0 := fun e => hS (by rw [e]; simp)
  have h2 : l ≠ 0 := fun e => hS (by rw [e]; simp)
  field_simp

end Norm

end GlobalTheory.NormRatio
