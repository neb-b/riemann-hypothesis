module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatible
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LieBasisRing

open GlobalTheory.KSExist.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isSplitting_embS {l : Level H} (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => (algebraMap c.F S).comp (embK c σ) := by
  refine EigenSplit.isSplitting_of_isDomain (S := c.F) (σ := fun σ : E →+* ℂ => embK c σ) (fun σ σ' e => ?_)
    (NumberField.Embeddings.card E ℂ) _ ?_
  · have e' : embF c σ = embF c σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e
    ext x
    have := congrArg (fun f : E →+* c.F => ((f x : c.F) : ℂ)) e'
    exact this
  · have : IsUnit ((NumberField.discr E : ℤ) : c.F) :=
      isUnit_iff_ne_zero.2 (by exact_mod_cast NumberField.discr_ne_zero E)
    simpa using this.map (algebraMap c.F S)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
  {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}

theorem isCombAt_of_isLieComb (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR S ⟶ A))
    (cf : Fin n → S) (w : epsR S ⟶ A) (h : IsLieComb cf v w) :
    IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => pushHom hπ (epsR S) (u i), fun i => ?_, (push_prod hπ u).symm⟩
  show (u i).left ≫ π = _
  rw [hu i, Category.assoc]
  rfl

end GlobalTheory.LieBasisRing

namespace GlobalTheory.LieBasisRing

theorem span_eq_top {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O]
    (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* S} (hχ : EigenSplit.IsSplitting χ)
    {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR S ⟶ A)) (hub : ∀ σ k, IsTangent (ub σ k))
    (hbasis : ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w) :
    Submodule.span S (Set.range fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)) = ⊤ := by
  let ρ : O →+* Module.End S (Serre.Lie a) := Module.toModuleEnd S (S := O) (Serre.Lie a)
  rw [eq_top_iff]
  intro x _
  rw [← EigenSplit.sum_proj hχ ρ x]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hx := EigenSplit.proj_mem hχ ρ σ x
  obtain ⟨cf, hcf⟩ := hbasis σ (EigenSplit.proj hχ ρ σ x).hom (EigenSplit.proj hχ ρ σ x).isTangent fun z =>
    congrArg Serre.Lie.hom (EigenSplit.mem_eigenSub.1 hx z)
  have e : EigenSplit.proj hχ ρ σ x = ∑ i, cf i • Serre.Lie.mk a (ub σ i) (hub σ i) :=
    Serre.Lie.ext ((Serre.Lie.isLieComb_iff cf (fun i => Serre.Lie.mk a (ub σ i) (hub σ i)) _).1 hcf)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, i⟩, rfl⟩)

theorem linearIndependent {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] [IsCommMonObj A] {O : Type}
    [CommRing O] (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* S}
    (hχ : EigenSplit.IsSplitting χ) {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR S ⟶ A))
    (hub : ∀ σ k, IsTangent (ub σ k))
    (heig : ∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ ub σ k)
    (huniq : ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∀ cf cf', IsLieComb cf (ub σ) w → IsLieComb cf' (ub σ) w → cf = cf') :
    LinearIndependent S fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _) := by
  let ρ : O →+* Module.End S (Serre.Lie a) := Module.toModuleEnd S (S := O) (Serre.Lie a)
  let v : (Σ σ, Fin (m σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)
  have hmem : ∀ k, v k ∈ EigenSplit.eigenSub ρ (χ k.1) := fun k =>
    EigenSplit.mem_eigenSub.2 fun z => Serre.Lie.ext (heig k.1 k.2 z)
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  obtain ⟨σ, i⟩ := k
  have h1 := congrArg (EigenSplit.proj hχ ρ σ) hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, Fintype.sum_sigma] at h1
  have h2 : ∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩ = 0 := by
    rw [← h1, Finset.sum_eq_single σ]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, EigenSplit.proj_of_mem hχ (hmem ⟨σ, j⟩)]
    · intro σ' _ hσ'
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, EigenSplit.proj_of_mem_ne hχ hσ' (hmem ⟨σ', j⟩), smul_zero]
    · intro h; exact absurd (Finset.mem_univ σ) h
  have hw : ∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩ ∈ EigenSplit.eigenSub ρ (χ σ) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem ⟨σ, j⟩)
  have c1 : IsLieComb (fun j => g ⟨σ, j⟩) (ub σ) (∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩).hom :=
    (Serre.Lie.isLieComb_iff _ (fun j => v ⟨σ, j⟩) _).2 rfl
  have c0 : IsLieComb (0 : Fin (m σ) → S) (ub σ) (∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩).hom :=
    (Serre.Lie.isLieComb_iff _ (fun j => v ⟨σ, j⟩) _).2 (by rw [h2]; simp)
  have := huniq σ _ (Serre.Lie.isTangent _) (fun z => congrArg Serre.Lie.hom (EigenSplit.mem_eigenSub.1 hw z))
    _ _ c1 c0
  exact congrFun this i

end GlobalTheory.LieBasisRing

namespace GlobalTheory.LieBasisRing

open GlobalTheory.KSExist.FrameLift

theorem lifts_basis_mod_fil : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left},
    IsGrpPullback A Xo.univ.t.G y.x π →
    ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) →
    ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) →
    Submodule.span S (Set.range hb) ⊔ Fil A = ⊤ ∧
      LinearIndependent S (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  intro P E _ _ _ H Dw l Xo c S _ _ y A _ π hπ ub hub hb hhb
  classical
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have : IsCommMonObj A := hA.comm
  obtain ⟨a, ha⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback Xo.univ.t.act hπ
  have htan : ∀ σ k, IsTangent (ub σ k) := fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k)
  have heig : ∀ σ k z, ub σ k ≫ a.act z =
      GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ ub σ k := fun σ k z =>
    (eig_iff hπ (ha z) _ _).1 (by rw [hub]; exact y.eig σ k z)
  have eu : ∀ σ, y.u σ = fun i => (ub σ i).left ≫ π := fun σ => funext fun i => (hub σ i).symm
  have hbasis : ∀ σ (w : epsR S ⟶ A), IsTangent w →
      (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w := by
    intro σ w ht he
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [eu σ] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩
  have huniq : ∀ σ (w : epsR S ⟶ A), IsTangent w →
      (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ w) →
      ∀ cf cf', IsLieComb cf (ub σ) w → IsLieComb cf' (ub σ) w → cf = cf' := by
    intro σ w ht he cf cf' h h'
    obtain ⟨cf₀, -, hu⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    have k := isCombAt_of_isLieComb hπ _ cf w h
    have k' := isCombAt_of_isLieComb hπ _ cf' w h'
    rw [← eu σ] at k k'
    exact (hu cf k).trans (hu cf' k').symm
  have L := (P.2.1 S A _ hA gA).1
  let v : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub k.1 k.2) (htan _ _)
  have hχ := isSplitting_embS (E := E) c S
  have hspan : Submodule.span S (Set.range v) = ⊤ := span_eq_top a hχ ub htan hbasis
  have hind : LinearIndependent S v := linearIndependent a hχ ub htan heig huniq
  have hv : (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = (L.quotEquiv a).symm ∘ v := by
    funext k
    rw [Function.comp_apply, LinearEquiv.eq_symm_apply, LieExact.quotEquiv_mk, L.toLie_eq_iff]
    exact hhb k
  refine ⟨?_, hv ▸ hind.map' _ (L.quotEquiv a).symm.ker⟩
  have h1 : Submodule.map (Fil A).mkQ (Submodule.span S (Set.range hb)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span S (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = ⊤
    rw [hv, Set.range_comp, eq_top_iff]
    intro q _
    have hq : (L.quotEquiv a) q ∈ Submodule.span S (Set.range v) := hspan ▸ Submodule.mem_top
    simpa using hq
  have h2 := congrArg (Submodule.comap (Fil A).mkQ) h1
  rwa [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] at h2

end GlobalTheory.LieBasisRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueGeLocalDepthPrimeToP
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.TermLoc

theorem harmonic_value_ge_local_depth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA (Dw := Dw) c w n → (∀ k, (ρ : EReal) ≤ nuLocOf C e k (MvPolynomial.map io P)) → ∀ (N : ℕ), Odd N → IsUnit (N : T.V) → ∀ (x₂ : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ b, x₂ b ^ (N ^ 2) = 1 ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) 1 (x₂ b) (F b)) → letI := io.toAlgebra; (ρ : EReal) ≤ nval T.V e (hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hC nab hnab e ρ w n he P hP hloc N hN hu x₂ F hF
  letI := io.toAlgebra
  have hst : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hone : ∀ {Z : Over Xo.X} (t : Z ⟶ Xo.univ.t.G), t ≫ Xo.univ.t.act.act 1 = t := fun t => by
    rw [Xo.univ.t.act.one, Category.comp_id]
  have hmix := fun b => (_root_.GlobalTheory.PlaceInt.uu_eq_pull_reach E H Dw l Xo T.Fr (xOf y) N N 1 1 1 1 hN (by simp) (by simp) (by simp)
    (sOf1 y) 1 (x₂ b) (F b) (one_pow _) (hF b).1 (by rw [_root_.mul_one, hone, one_pow]) (by rw [hone, _root_.mul_one]; exact (hF b).1)
    (hF b).2).2
  choose hh hre hpl using hmix
  have hg := fun b => (GlobalTheory.T.regular_section_integral_germ_unique_scale E H Dw l Xo c hst T io y C hC.1 _ (hh b)).1
    (_root_.GlobalTheory.ReachRegular.regular_of_reach E H Dw l Xo c hst T io y C hC _ (hh b) (hre b))
  choose f hf using hg
  obtain ⟨B, hB1, -⟩ := GlobalTheory.T.integralChart_formalBiextension_gauge_bound E H Dw l Xo c hst T io y C
  have hHH : P ∈ HH c w n := hP.1
  have hni := GlobalTheory.T.harmonicValue_integralPoint_eq_value_on_biextensionCopies E H Dw l Xo c hst T io y C nab hnab B hB1 _ n hh f hf w P hHH
  have hch := _root_.GlobalTheory.PlaceInt.hv_pulls E H Dw l Xo c hst nab hnab T.Fr y.1 1 1 (N ^ 2 * 1) (N ^ 2) (by simp) (by ring) n hh
    (fun b => sqN Xo N (F b)) hpl w P hHH
  have hn1 : nrm Dw c w (1 : 𝓞 E) = 1 := by simp [nrm]
  rw [hch, hn1, map_one, _root_.one_mul, hni]
  obtain ⟨hF', hA', -, -, -, -, -⟩ := C.gen.1
  obtain ⟨e1, e2, -, -, -, -⟩ := hB1
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [GlobalTheory.ChartBiext.toK_self, hF', e1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [GlobalTheory.ChartBiext.toK_self, hA', e2]
  rw [GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA]
  refine (hloc (N ^ 2 * 1)).trans ?_
  unfold nuLocOf
  refine iInf_le_of_le (FB.toK T.Fr (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))) (iInf_le_of_le ?_ le_rfl)
  intro m
  exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

end GlobalTheory.RefSum.TermLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterConjHalfIdeleEqProdLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumChar

open Formalism.L2.JoinChr

theorem locE_sum {D : D7} {ι : Type} (s : Finset ι) (f : ι → AE D)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) (k : D.host.E) :
    locE D (∑ i ∈ s, f i) k = ∏ i ∈ s, locE D (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [locE]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ← ih fun i hi j hj hij => hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : f a * ∑ i ∈ s, f i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i hi => hf a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    unfold locE
    linear_combination (-(incA D k - 1) * (incA D k - 1)) * h0

theorem char_eq_prod : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (eQ : AE D), IsIdemSum eQ Q → ∀ (k : D.host.Eˣ) (y : (AE D)ˣ), (y : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (k : D.host.E) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → ((c y : Circle) : ℂ) = ∏ P ∈ Q, ((ψ.locK (conjPl P) k : ℂˣ) : ℂ) := by
  intro D Q eQ h k y hy c ψ hψ
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hIP : ∀ P ∈ Q, Formalism.L2.NTheta.IsIdemAt (cA D (es P)) (conjPl P) := fun P hP =>
    GlobalTheory.MovedIdem.isIdemAt_conj (hes P hP) fun _ => Iff.rfl
  let g : Pl D.host.E → AE D := fun P => if P ∈ Q then cA D (es P) else 0
  have hg : ∀ P, g P * g P = g P := fun P => by
    by_cases hP : P ∈ Q
    · simp only [g, if_pos hP]; exact (hIP P hP).1.1
    · simp only [g, if_neg hP, mul_zero]
  have horth : ∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → g P * g P' = 0 := fun P hP P' hP' hne => by
    simp only [g, if_pos hP, if_pos hP', ← map_mul]
    rw [idem_orth (idemAt_split (hes P hP)) (hes P hP) (hes P' hP') hne, map_zero]
  have hsum : cA D (∑ P ∈ Q, es P) = ∑ P ∈ Q, g P := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun P hP => by simp only [g, if_pos hP]
  have hy' : y = ∏ P ∈ Q, locU (hg P) k := by
    apply Units.ext
    rw [hy, Units.coe_prod, hsum, locE_sum Q g horth]
    rfl
  rw [hy', map_prod]
  have hcoe : ∀ (s : Finset (Pl D.host.E)) (u : Pl D.host.E → Circle),
      (((∏ P ∈ s, u P : Circle)) : ℂ) = ∏ P ∈ s, ((u P : Circle) : ℂ) := fun s u =>
    map_prod Circle.coeHom u s
  rw [hcoe]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hpl : IsPlIdem D (g P) (conjPl P) := by
    simp only [g, if_pos hP]; exact GlobalTheory.HeckeDetChar.isPlIdem (hIP P hP)
  exact hψ.2 (conjPl P) (g P) hpl k (locU (hg P) k) (locU_val _ _)

end GlobalTheory.IdemSumChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerate
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem modif_genericPoint {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) [IsIntegral M.X] {η : Y} (hη : η ∈ U) (hg : IsGenericPoint η Set.univ) :
    M.σ (genericPoint M.X) = η ∧ genericPoint M.X ∈ M.opn ∧ IsIso (M.σ.stalkMap (genericPoint M.X)) := by
  have := M.iso
  have hne : (M.opn : Set M.X).Nonempty := M.dense.nonempty
  have hmem : genericPoint M.X ∈ M.opn :=
    ((genericPoint_spec M.X).mem_open_set_iff M.opn.isOpen).2 (by simpa using hne)
  obtain ⟨z, hz⟩ := (M.σ ∣_ U).surjective ⟨η, hη⟩
  have hz' : M.σ z.1 = η := by rw [← morphismRestrict_base_coe, hz]
  have hsp : M.σ (genericPoint M.X) ⤳ η :=
    hz' ▸ ((genericPoint_spec M.X).specializes (Set.mem_univ z.1)).map M.σ.continuous
  have he : M.σ (genericPoint M.X) = η := (hsp.antisymm (hg.specializes (Set.mem_univ _))).eq
  refine ⟨he, hmem, ?_⟩
  let z0 : (M.σ ⁻¹ᵁ U).toScheme := ⟨genericPoint M.X, hmem⟩
  have h1 : IsIso ((M.σ ∣_ U ≫ U.ι).stalkMap z0) := by
    rw [Scheme.Hom.stalkMap_comp]
    have a := (IsOpenImmersion.iff_isIso_stalkMap.1 (inferInstance : IsOpenImmersion U.ι)).2 ((M.σ ∣_ U) z0)
    have b := (IsOpenImmersion.iff_isIso_stalkMap.1 (inferInstance : IsOpenImmersion (M.σ ∣_ U))).2 z0
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ a b
  rw [morphismRestrict_ι, Scheme.Hom.stalkMap_comp] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    ((IsOpenImmersion.iff_isIso_stalkMap.1 (inferInstance : IsOpenImmersion (M.σ ⁻¹ᵁ U).ι)).2 z0) h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem birational_of_ratGen {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7}
    (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r)
    (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec)
    (k : Consts) (hR : RatGen X Z U P.u₁) : (h.geo f₁ f₂ th k).Birational := by
  obtain ⟨η, hη, hgen, hrat⟩ := hR
  haveI : IsIntegral R.X := HilbertSamuel.Geo.isIntegral (h.geo f₁ f₂ th k)
  obtain ⟨he, hmem, hiso⟩ := modif_genericPoint R.toModif hη hgen
  subst he
  set G := h.geo f₁ f₂ th k with hG
  set η' := genericPoint R.X with hη'
  refine ⟨η', genericPoint_spec _, ?_⟩
  set xp : Sp (R.X.residueField η') ⟶ G.Y := resPt η' with hxp
  set cc := G.chartAt (ptOf xp) with hcc
  have hc : η' ∈ R.Δ₁.moving.U cc := (ptOf_resPt η') ▸ G.mem_chartAt (ptOf xp)
  have hi0 : R.σ η' ∈ (L₀ X Z P.u₁).U (cc.1 PUnit.unit) := mem_pull.1 hc.1
  set φ := (R.σ.residueFieldMap η').hom with hφdef
  have hφ : ∀ a, φ (((Y₀ X Z).residue (R.σ η')).hom a) = (R.X.residue η').hom ((R.σ.stalkMap η').hom a) := fun a => by
    have := congrArg (fun g => g.hom a) (Scheme.residue_residueFieldMap R.σ η')
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this

  let Vf : Cusp Z U P.u₁ → R.X.residueField η' := fun f => G.val xp (toSec (R.Δ₁.lift (h.ext₁.equiv f)))
  have hA : ∀ f, Vf f = ∑ j, G.baseHom xp (f₁.b.equivFun f j) * G.coords xp j := by
    intro f
    have e := R.toModif.ofSec_comb R.Δ₁ h.ext₁.equiv f₁ k.abelian₂ (f₁.b.equivFun f)
    rw [LinearEquiv.symm_apply_apply] at e
    have e2 : toSec (R.Δ₁.lift (h.ext₁.equiv f)) = G.comb (f₁.b.equivFun f) := by
      apply (bijective_ofSec_top (p := R.str) (B := R.Δ₁.moving)).1
      rw [ofSec_toSec]
      exact e.symm
    exact (congrArg (G.val xp) e2).trans (G.val_comb xp _)
  have hV : ∀ f, Vf f = (R.X.residue η').hom (germ cc η' (memTop η') hc (R.Δ₁.lift (h.ext₁.equiv f))) := by
    intro f
    show valR xp _ _ = _
    refine (projSys.valR_resPt η' _ hc _).trans ?_
    refine (congrArg (fun g => (ConcreteCategory.hom g) ((toSec (R.Δ₁.lift (h.ext₁.equiv f))).f cc))
      (Scheme.germ_residue R.X η' hc).symm).trans ?_
    exact congrArg (R.X.residue η').hom (ger_toSec _ cc η' hc)
  set τ := (R.X.residue η').hom (ger η' hc.2 (R.Δ₁.t.f cc.2)) with hτdef
  have hB : ∀ f, τ * Vf f = φ (((Y₀ X Z).residue (R.σ η')).hom
      (germ (cc.1 PUnit.unit) (R.σ η') hη hi0 (cuspSec X Z U P.u₁ f))) := by
    intro f
    have e1 := R.Δ₁.germ_lift (h.ext₁.equiv f) cc η' hc
    have e2 := germ_pull R.σ le_top cc.1 η' (memTop η') hc.1 (h.ext₁.equiv f).1
    have e3 := hφ (germ (cc.1 PUnit.unit) (R.σ η') (memTop _) hi0 (h.ext₁.equiv f).1)
    have e4 : germ (cc.1 PUnit.unit) (R.σ η') hη hi0 (cuspSec X Z U P.u₁ f) =
        germ (cc.1 PUnit.unit) (R.σ η') (memTop _) hi0 (h.ext₁.equiv f).1 := by
      rw [← h.ext₁.restr_equiv f, germ_restr]
    rw [hV, e4, e3, ← e2, ← e1]
    exact (map_mul _ _ _).symm
  have hτ : τ ≠ 0 := by
    have hu : IsUnit (ger η' hc.2 (R.Δ₁.t.f cc.2)) :=
      (isUnit_ger_iff _ hc.2).2 ((R.Δ₁.mem_nonzeroLocus η').2 (R.notMem_support h.free₁ η' (R.off_eq.ge hmem)))
    exact (hu.map (R.X.residue η').hom).ne_zero
  obtain ⟨j₀, hj₀⟩ : ∃ j, G.coords xp j ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact G.geom.alg.bpf.coords_ne_zero xp (funext hn)
  have hmemV : ∀ f f', Vf f / Vf f' ∈ G.ratioField xp := by
    intro f f'
    have key : ∀ g, Vf g = G.coords xp j₀ *
        ∑ j, G.baseHom xp (f₁.b.equivFun g j) * (G.coords xp j / G.coords xp j₀) := by
      intro g
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    have hs : ∀ g, ∑ j, G.baseHom xp (f₁.b.equivFun g j) * (G.coords xp j / G.coords xp j₀) ∈ G.ratioField xp :=
      fun g => Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (Subfield.subset_closure (Or.inl ⟨_, rfl⟩))
        (Subfield.subset_closure (Or.inr ⟨j, j₀, rfl⟩))
    rw [key, key, mul_div_mul_left _ _ hj₀]
    exact Subfield.div_mem _ (hs f) (hs f')
  have hgen' : ratField (Set.range (cuspSec X Z U P.u₁)) (R.σ η') hη ≤ (G.ratioField xp).comap φ := by
    refine Subfield.closure_le.2 ?_
    rintro _ ⟨i, hi, _, _, ⟨f, rfl⟩, ⟨f', rfl⟩, rfl⟩
    have htr : ((Y₀ X Z).residue (R.σ η')).hom (tr (L₀ X Z P.u₁) (R.σ η') i (cc.1 PUnit.unit) : _) ≠ 0 :=
      ((Units.isUnit _).map _).ne_zero
    show φ (_ / _) ∈ G.ratioField xp
    rw [germ_change i (cc.1 PUnit.unit) _ hη hi hi0, germ_change i (cc.1 PUnit.unit) _ hη hi hi0, map_mul, map_mul,
      mul_div_mul_left _ _ htr, map_div₀, ← hB f, ← hB f', mul_div_mul_left _ _ hτ]
    exact hmemV f f'
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨a', rfl⟩ := R.X.residue_surjective η' y
  obtain ⟨a, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 hiso).2 a'
  rw [← hφ]
  exact hgen' (hrat.ge trivial)

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledVacuumConditionUniqueStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_doubledVacuumCondition_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → ∃ c : ℂ, φ = c • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) := by
  first | exact @GlobalTheory.DblVacUniq.dbl_vac_unique | exact GlobalTheory.DblVacUniq.dbl_vac_unique | (intros; apply GlobalTheory.DblVacUniq.dbl_vac_unique <;> assumption)
end

