module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobou
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOffClosedSubset
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.GenericChart

theorem exists_isClosed_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∃ T : Set X, IsClosed T ∧ genericPoint X ∉ T ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), y.1 (IsLocalRing.closedPoint ℂ) ∉ T → ∃ c : AlgChart p σ D, y ∈ c.e.source := by
  intro k _ X _ p D h
  obtain ⟨U, hU, hη, t, ht⟩ := GlobalTheory.GenericCoords.exists_affine_etale_coords h
  refine ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl, fun h' => h' hη, fun σ y hy => ?_⟩
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale (σ := σ) hU t ht (y := y)
    (mem_ptsIn.2 (not_not.1 hy))
  exact ⟨c, hc⟩

end GlobalTheory.GenericChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenKernelStableHarrisTaylor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_clopen_kerStableAt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ KerStableAt o ψ t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [← Nat.cast_pow, map_natCast, ← he] at this
    exact this
  haveI : IsMonHom ψ := hq.1
  haveI : IsMonHom ψ' := hq.2.1
  haveI := D.finO
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := D.O)
  have key : ∀ a : D.O, ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y),
      Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ g : T ⟶ o.A,
        g ^ c = 1 → g ≫ ψ = 1 → g ≫ o.act.act a ≫ ψ = 1 := by
    intro a
    haveI := o.act.hom a
    obtain ⟨W, hW1, hW2, hW, -⟩ := GlobalTheory.LevCover.kerlocus_open_closed Y o.A c Unit (fun _ => B) (fun _ => ψ) B
      (o.act.act a ≫ ψ) o.ab (fun _ => hB) hB (fun _ => inferInstance) inferInstance hc
    refine ⟨W, hW1, hW2, fun Tb t => (hW Tb t).trans ?_⟩
    simp only [forall_const]
  choose W hW1 hW2 hW using key
  have hkill : ∀ (T : Over Y) (g : T ⟶ o.A), g ≫ ψ = 1 → g ^ c = 1 := by
    intro T g hg
    have h1 : g ^ c = g ≫ (𝟙 o.A) ^ c := by rw [MonObj.comp_pow, Category.comp_id]
    rw [h1, ← hq.2.2.1, ← Category.assoc, hg, MonObj.one_comp]
  refine ⟨⋂ a ∈ S, W a, isOpen_biInter_finset (fun a _ => hW1 a),
    isClosed_iInter fun a => isClosed_iInter fun _ => hW2 a, fun Tb t => ?_⟩
  rw [Set.subset_iInter₂_iff]
  constructor
  · intro h T σ hσ g hg a
    let f : D.O →+ Additive (T ⟶ B) := AddMonoidHom.mk' (fun a => Additive.ofMul (g ≫ o.act.act a ≫ ψ))
      (fun a a' => by
        rw [o.act.add]
        haveI := o.act.hom a
        haveI := o.act.hom a'
        rw [MonObj.mul_comp, MonObj.comp_mul]
        rfl)
    have hSk : (S : Set D.O) ⊆ (f.toIntLinearMap.ker : Set D.O) := fun a ha => by
      have := (hW a Tb t).1 (h a ha) T σ hσ g (hkill T g hg) hg
      simp [f, this]
    have htop : (⊤ : Submodule ℤ D.O) ≤ LinearMap.ker f.toIntLinearMap := by
      rw [← hS]; exact Submodule.span_le.mpr hSk
    have ha : f a = 0 := htop Submodule.mem_top
    simpa [f] using ha
  · intro h a _
    exact (hW a Tb t).2 fun T σ hσ g _ hg => h T σ hσ g hg a

end GlobalTheory.UPel.HT.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundarySndTr
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CocInv

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

def affVal (V : A.left.affineOpens) (P : GPt A) (h : P.In V.1) : (Pt.aff (A.hom ≫ 𝟙 (Sp K)) V).Hom P where
  ρ := { (GlobalTheory.Points.valMap P.x V.1 (show ⊤ ≤ P.x ⁻¹ᵁ V.1 from h)).hom with
    commutes' := fun r ↦
      (GlobalTheory.Points.valR_eq P.x V.1 h (constFn (A.hom ≫ 𝟙 (Sp K)) V.1 r)).symm.trans
        (GlobalTheory.Points.valR_constFn_of_over _ (algebraMap K P.B) P.x P.w V.1 h r) }
  pt := GlobalTheory.Points.specMap_valMap_fromSpec V.2 P.x h

theorem affVal_ρ (V : A.left.affineOpens) (P : GPt A) (h : P.In V.1) (f : CechDR.Sec (A.hom ≫ 𝟙 (Sp K)) V.1) :
    (affVal V P h).ρ f = valR P.x V.1 f :=
  (GlobalTheory.Points.valR_eq P.x V.1 h f).symm

theorem affVal_comp (V : A.left.affineOpens) {P Q : GPt A} (h : P.In V.1) (φ : P.Hom Q) :
    (affVal V P h).comp φ = affVal V Q (h.map φ) := by
  have e : ((affVal V P h).comp φ).ρ = (affVal V Q (h.map φ)).ρ := by
    ext f
    change φ.ρ ((affVal V P h).ρ f) = _
    rw [affVal_ρ, affVal_ρ, ← φ.pt]
    exact (GlobalTheory.Points.valR_spMap_comp (φ.ρ : P.B →+* Q.B) P.x V.1 h f).symm
  cases h1 : (affVal V P h).comp φ
  cases h2 : affVal V Q (h.map φ)
  rw [h1, h2] at e
  cases e
  rfl

theorem aff_in (V : A.left.affineOpens) : (Pt.aff (A.hom ≫ 𝟙 (Sp K)) V).In V.1 :=
  V.2.fromSpec_preimage_self.ge

def Idx {I : Type} (U : I → A.left.Opens) : Type := {p : I × A.left.affineOpens // p.2.1 ≤ U p.1}


omit [GrpObj A] in
theorem iSup_idx {I : Type} (U : I → A.left.Opens) (hU : ⨆ i, U i = ⊤) : ⨆ a : Idx U, a.1.2.1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ ⨆ i, U i := hU.ge trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    A.left.isBasis_affineOpens.exists_subset_of_mem_open hi (U i).2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, ⟨V, hV⟩), hVU⟩, hxV⟩


open Classical in
def βa {I : Type} {U : I → A.left.Opens} (β : ∀ P Q : GPt A, P.Hom Q → Q.B) (a : Idx U) :
    PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ if h : P.In a.1.2.1 then β _ P (affVal a.1.2 P h) else 0

theorem βa_step {I : Type} {U : I → A.left.Opens} {β : ∀ P Q : GPt A, P.Hom Q → Q.B}
    (hβ : ∀ (P Q T : GPt A) (φ : P.Hom Q) (ψ : Q.Hom T), (∃ i, P.In (U i)) →
      β P T (φ.comp ψ) = ψ.ρ (β P Q φ) + β Q T ψ) (a : Idx U) {P Q : GPt A} (h : P.In a.1.2.1)
    (φ : P.Hom Q) : βa β a Q = φ.ρ (βa β a P) + β P Q φ := by
  have hQ : Q.In a.1.2.1 := h.map φ
  simp only [βa, dif_pos h, dif_pos hQ]
  rw [← affVal_comp a.1.2 h φ]
  exact hβ _ P Q _ φ ⟨a.1.1, (aff_in a.1.2).mono a.2⟩


open Classical in
theorem exists_coboundary_snd_tr : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) (U : I → A.left.Opens), ⨆ i, U i = ⊤ → ∀ β : ∀ P Q : GPt A, P.Hom Q → Q.B, (∀ (P Q T : GPt A) (φ : P.Hom Q) (ψ : Q.Hom T), (∃ i, P.In (U i)) → β P T (φ.comp ψ) = ψ.ρ (β P Q φ) + β Q T ψ) → ∀ v : epsR K ⟶ A, IsTangent v → ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (i : I) (V : A.left.affineOpens), V.1 ≤ U i → ∀ (P Q : GPt A) (φ : P.Hom Q), P.In V.1 → TrivSqZeroExt.snd (R := Q.B) (β (P.tr v) (Q.tr v) (φ.tr v)) = G Q - φ.ρ (G P) := by
  intro K _ A _ hA I U hU β hβ v hv
  let W : Idx U → A.left.Opens := fun a ↦ a.1.2.1

  have hsec : ∀ a b : Idx U, ∃ f : Γ(A.left, W a ⊓ W b), ∀ P : GPt A, P.In (W a ⊓ W b) →
      βa β a P - βa β b P = valR P.x (W a ⊓ W b) f := by
    intro a b
    obtain ⟨f, hf⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K A.left (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ W a ⊓ W b) (W a ⊓ W b)
      (fun _ ↦ le_rfl) (le_iSup (fun _ : Unit ↦ W a ⊓ W b) ()) (fun P ↦ βa β a P - βa β b P) (fun _ P Q φ hP ↦ by
        change βa β a Q - βa β b Q = φ.ρ (βa β a P - βa β b P)
        rw [βa_step hβ a (hP.mono inf_le_left) φ, βa_step hβ b (hP.mono inf_le_right) φ, map_sub]
        ring)
    exact ⟨f, fun P hP ↦ hf () P hP⟩
  choose φab hφab using hsec
  have hcoc : ∀ (a b c : Idx U) (P : GPt A), P.In (W a) → P.In (W b) → P.In (W c) →
      valR P.x _ (φab a b) + valR P.x _ (φab b c) = valR P.x _ (φab a c) := by
    intro a b c P ha hb hc
    rw [← hφab a b P (ha.inf hb), ← hφab b c P (hb.inf hc), ← hφab a c P (ha.inf hc)]
    ring
  obtain ⟨ψ, hψn, hψ⟩ := _root_.GlobalTheory.CechInv.deriv_cocycle_isCoboundary K A hA (Idx U) W (iSup_idx U hU) φab hcoc v hv
  let G : PtFn (A.hom ≫ 𝟙 (Sp K)) := fun P ↦
    if h : ∃ a, P.In (W a) then TrivSqZeroExt.snd (R := P.B) (βa β h.choose (P.tr v)) - ψ h.choose P else 0
  have hG : ∀ (a : Idx U) (P : GPt A), P.In (W a) →
      G P = TrivSqZeroExt.snd (R := P.B) (βa β a (P.tr v)) - ψ a P := by
    intro a P ha
    have h : ∃ a, P.In (W a) := ⟨a, ha⟩
    have hb : P.In (W h.choose) := h.choose_spec
    have e1 := hφab h.choose a (P.tr v) ((hb.inf ha).tr hv)
    have e2 := hψ h.choose a P hb ha
    change βa β h.choose (P.tr v) - βa β a (P.tr v) = valR (P.trx v) _ (φab h.choose a) at e1
    rw [← e1, TrivSqZeroExt.snd_sub] at e2
    simp only [G, dif_pos h]
    linear_combination e2
  refine ⟨G, fun i V hVU P Q φ hP ↦ ?_⟩
  let a : Idx U := ⟨(i, V), hVU⟩
  have hPa : P.In (W a) := hP
  have hQa : Q.In (W a) := hP.map φ
  rw [hG a P hPa, hG a Q hQa, hψn a P Q φ hPa]
  have e := βa_step hβ a (hPa.tr hv) (φ.tr v)
  have e' := congrArg (TrivSqZeroExt.snd (R := Q.B)) e
  change TrivSqZeroExt.snd (R := Q.B) (βa β a (Q.tr v)) =
    TrivSqZeroExt.snd (R := Q.B) (dualAlg φ.ρ (βa β a (P.tr v)) + β (P.tr v) (Q.tr v) (φ.tr v)) at e'
  rw [TrivSqZeroExt.snd_add, snd_dualAlg] at e'
  rw [map_sub]
  linear_combination -e'

end GlobalTheory.CocInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientDataOfNonzeroSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem integral_of_sqPow_bdd (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (y : FractionRing R) (r : R) (hr : r ≠ 0)
    (h : ∀ n : ℕ, ∃ s : R, algebraMap R (FractionRing R) r * y ^ (n ^ 2) = algebraMap R _ s) :
    ∃ s : R, y = algebraMap R _ s := by
  set c : FractionRing R := algebraMap R (FractionRing R) r with hc
  have hc0 : c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  have hall : ∀ k : ℕ, ∃ s : R, c ^ 4 * y ^ k = algebraMap R _ s := by
    intro k
    obtain ⟨p, q, u, v, hk⟩ := Nat.sum_four_squares k
    obtain ⟨s1, h1⟩ := h p
    obtain ⟨s2, h2⟩ := h q
    obtain ⟨s3, h3⟩ := h u
    obtain ⟨s4, h4⟩ := h v
    refine ⟨s1 * s2 * s3 * s4, ?_⟩
    rw [← hk, map_mul, map_mul, map_mul, ← h1, ← h2, ← h3, ← h4, pow_add, pow_add, pow_add]
    ring
  let S : Subalgebra R (FractionRing R) := Algebra.adjoin R {y}
  have hle : Subalgebra.toSubmodule S ≤ Submodule.span R {(c ^ 4)⁻¹} := by
    show Subalgebra.toSubmodule (Algebra.adjoin R {y}) ≤ _
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro z hz
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hz
    obtain ⟨s, hs⟩ := hall k
    have hc4 : c ^ 4 ≠ 0 := pow_ne_zero _ hc0
    have : y ^ k = s • (c ^ 4)⁻¹ := by
      rw [Algebra.smul_def, ← hs]; field_simp
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
  have hfg : (Subalgebra.toSubmodule S).FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span_singleton (R := R) ((c ^ 4)⁻¹ : FractionRing R))
    have h1 : ((Subalgebra.toSubmodule S).comap (Submodule.span R {(c ^ 4)⁻¹}).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Submodule.span R {(c ^ 4)⁻¹}).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  have hint : IsIntegral R y := IsIntegral.of_mem_of_fg S hfg y (Algebra.self_mem_adjoin_singleton R y)
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨s, hs.symm⟩

theorem exists_coefData_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left), GlobalTheory.LN.Cmp φ U U' F → GlobalTheory.LN.CDvr V → Function.Injective φ → (maximalIdeal V).comap φ = maximalIdeal R → GlobalTheory.LN.Under U' U₀.toUnifPre → ∃ (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 ∧ U.ExpT (𝟙_ _) 1 σ f ∧ (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) ∧ GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) ∧ ∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h := by

  intro R _ _ _ hB D A G _ _ U V _ _ _ φ D' A' G' _ _ U' U₀ F C hV hφ hI hU
  obtain ⟨⟨h₁, h₂, -, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_of_laws h₁ h₂
  have hR : AdmBase R (maximalIdeal R) := hB.1
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  have hmR : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  have := hV.1
  have hV' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hm : maximalIdeal V ≠ ⊤ := (maximalIdeal.isMaximal V).ne_top
  have hIm : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hI.ge
  obtain ⟨σ, hσ0⟩ := _root_.GlobalTheory.Mum.ModelSection.main R hB D A G U
  obtain ⟨f, hf, -⟩ := GlobalTheory.CompleteBaseExpansion.main h₁ h₂ hE R _ hR hmR D A G U 1 σ
  obtain ⟨σ', f', hf', hσσ, hff⟩ := GlobalTheory.ExpCmp.expT_cmp R V _ _ φ hIm D D'.toPre A A' G G' U U' F C 1 σ f hf
  have hcmp : GlobalTheory.PsiRing.SecCmp D D'.toPre C.β C.v C.xe f f' := hff
  have hrel' := _root_.GlobalTheory.PsiExpansion.psiRel_of_expT h₁ h₂ V _ hV' D' A' G' U' U₀ hU σ' f' hf'
  have hσ'0 := _root_.GlobalTheory.PullNonzero.main R hB D A G U V φ D'.toPre A' G' U' F C hV hφ σ σ' hσσ hσ0
  have hne' : ∀ α, ∃ j, (f' α).f j ≠ 0 :=
    _root_.GlobalTheory.forall_ne_zero_of_psiRel V D'.toPre f' hrel' (_root_.GlobalTheory.ExpansionNonzero.exists_term_ne_zero V hV D' A' G' U' U₀ hU σ' f' hf' hσ'0)
  have hne := GlobalTheory.PsiRing.ne_zero_of_secCmp C.pbB.1.w hcmp hne'
  obtain ⟨psi, h, hrel⟩ := GlobalTheory.exists_psi_psiRel h₁ h₂ R D f hne
  let E : DegPre R := GlobalTheory.LN.withPsi D psi h
  have hrelE : GlobalTheory.UU.PsiRel E (𝟙_ _) f := hrel
  have hrig : GlobalTheory.PsiRing.RigCmp φ E D'.toPre C.β C.v := _root_.GlobalTheory.rigCmp_of_cmp R V _ _ φ hm hIm D D'.toPre A G A' G' U U' F C
  obtain ⟨gam, hgam⟩ := GlobalTheory.PsiRing.exists_generic_map hφ
  have hpsi : GlobalTheory.PsiRing.PsiCmp E D'.toPre C.β C.v C.xe gam :=
    _root_.GlobalTheory.psiCmp_of_secCmp R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig f f' hcmp hrelE hrel' (hne' 0) gam hgam
  have hev : E.PsiEven :=
    _root_.GlobalTheory.PsiRing.psiEven_descend h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi D'.psi_even
  have hbi : E.TauBimult :=
    _root_.GlobalTheory.tauBimult_of_baseChange h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi D'.tau_bimult
  obtain ⟨ga, a, hS⟩ := GlobalTheory.exists_psiScal R E
  obtain ⟨th, hth, hmul⟩ := _root_.GlobalTheory.PsiRing.exists_basis_fibNZ h₂.secTwist R D
  obtain ⟨q, hq⟩ := hmul (f 0)
  choose b hb using fun χ : D.X => GlobalTheory.T.exists_twistedSection_thetaTranslate_coef R D th hmul χ (ga χ) (hS χ).1 (f χ)
  have hab : ∀ χ, algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) (b χ) := fun χ =>
    GlobalTheory.T.psiScalar_eq_expansionCoef_ratio R E ga a f th hS hrelE hth χ q (b χ) hq (hb χ)
  have hq0 : q ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne 0
    apply hj
    rw [_root_.GlobalTheory.PsiRing.secIsMul_of_mult R D th (f 0) 0 hq j]
    simp [scal]
  have hint : ∀ χ, ∃ c : R, ((a χ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ c := fun χ => by
    refine integral_of_sqPow_bdd R _ q hq0 fun n => ?_
    obtain ⟨u, hu⟩ := GlobalTheory.T.psiScalar_nsmul_eq_unit_mul_pow_sq R E ga a hS hev hbi χ n
    refine ⟨((u⁻¹ : Rˣ) : R) * b (n • χ), ?_⟩
    rw [map_mul, ← hab, hu]
    have hu1 : algebraMap R (FractionRing R) ((u⁻¹ : Rˣ) : R) * algebraMap R _ (u : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap R (FractionRing R) q * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2))) * hu1
  choose c hc using hint
  have hbc : ∀ χ, b χ = q * c χ := fun χ => by
    apply IsFractionRing.injective R (FractionRing R)
    exact (hab χ).symm.trans (by rw [map_mul, ← hc χ])
  have hcm : ∀ χ : D.X, χ ≠ 0 → c χ ∈ maximalIdeal R := fun χ hχ => by
    obtain ⟨x, rfl⟩ := C.xe.surjective χ
    obtain ⟨m, hm₁, hm₂⟩ := GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi ga a hS x _
      (D'.psi_pos x fun h0 => hχ (by rw [h0, map_zero])) _ q (hab _)
    have hm₃ : φ q * φ (c (C.xe x)) = φ q * m := by rw [← map_mul, ← hbc]; exact hm₂
    have hφq : φ q ≠ 0 := (map_ne_zero_iff _ hφ).2 hq0
    have e := mul_left_cancel₀ hφq hm₃
    have hmem : c (C.xe x) ∈ (maximalIdeal V).comap φ := Ideal.mem_comap.2 (by rw [e]; exact hm₁)
    exact (Set.ext_iff.1 (congrArg (fun J : Ideal R => (J : Set R)) hI) _).1 hmem
  choose G₁ hG₁ using fun χ : D.X => GlobalTheory.T.exists_translatedThetaCoefficient_section R D th χ (ga χ) (hS χ).1 (c χ)
  choose H₁ hH₁ using fun χ : D.X => GlobalTheory.T.exists_translatedThetaCoefficient_section R D th χ (ga χ) (hS χ).1 1
  classical
  let g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α := fun α => if h0 : α = 0 then h0 ▸ th else G₁ α
  refine ⟨σ, f, g, q, hq0, hf, fun α => ?_, ?_, fun α hα => ⟨c α, hcm α hα, H₁ α, ?_⟩⟩
  · by_cases h0 : α = 0
    · subst h0
      simp only [g, dif_pos rfl]
      exact _root_.GlobalTheory.PsiRing.secIsMul_of_mult R D th (f 0) q hq
    · simp only [g, dif_neg h0]
      exact GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional R D α (ga α) th (f α) (G₁ α) (b α) (c α) q (hb α) (hG₁ α) (hbc α)
  · simp only [g, dif_pos rfl]
    exact hth
  · simp only [g, dif_neg hα]
    exact GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional R D α (ga α) th (G₁ α) (H₁ α) (c α) 1 (c α) (hG₁ α) (hH₁ α) (_root_.mul_one _).symm

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonBaseChangeOfUOver
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem exists_common_baseChange_of_uOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (σ : R →+* K) (σ' : R' →+* K) (u : Sp K ⟶ Xo.XF cf), UOver Xo cf P σ u → UOver Xo cf P' σ' u → ∃ (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsGrpPullback P₀.A P.A (spMap σ) a ∧ IsGrpPullback P₀.A P'.A (spMap σ') a' ∧ LBIso P₀.L (P.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') := by
  intro E _ _ _ H Dw l Xo cf K R R' _ _ _ P P' σ σ' u h h'
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  obtain ⟨G', _, α', β', hα', hβ', hL'⟩ := h'
  obtain ⟨P₀, φ, hφ, hLφ⟩ := exists_pol_baseChange P (spMap σ)
  obtain ⟨e₀, _, he₀⟩ := grpPullback_iso hφ hα
  obtain ⟨e, _, he⟩ := grpPullback_iso hβ hβ'
  haveI : IsMonHom (e₀ ≪≫ e).hom := inferInstanceAs (IsMonHom (e₀.hom ≫ e.hom))
  have hU := Xo.univ.t.PP.isLB
  have X1 : LBIso (P.L.pull φ) (Xo.univ.t.PP.L.pull (e₀.hom.left ≫ β)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp e₀.hom.left he₀.symm rfl hL
  have X2 : LBIso (Xo.univ.t.PP.L.pull (e₀.hom.left ≫ β)) (P'.L.pull ((e₀.hom.left ≫ e.hom.left) ≫ α')) :=
    GlobalTheory.GenSpread.lbIso_pull_comp (e₀.hom.left ≫ e.hom.left) (by rw [← he, Category.assoc]) rfl hL'.symm
  refine ⟨P₀, φ, (e₀.hom.left ≫ e.hom.left) ≫ α', hφ,
    ((isGrpPullback_of_iso (e₀ ≪≫ e)).comp hα').congr (Category.id_comp _) rfl, hLφ,
    LBIso.trans P₀.isLB (pull_isLB P.isLB _) (pull_isLB P'.isLB _) hLφ
      (LBIso.trans (pull_isLB P.isLB _) (pull_isLB hU _) (pull_isLB P'.isLB _) X1 X2)⟩

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldOfFieldPointsSamePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_common_field_of_point_eq : ∀ (X : Scheme.{0}) (K₁ K₂ : Type) [Field K₁] [Field K₂] (a : Sp K₁ ⟶ X) (b : Sp K₂ ⟶ X), a (closedPoint K₁) = b (closedPoint K₂) → ∃ (Ω : Type) (_ : Field Ω) (i₁ : K₁ →+* Ω) (i₂ : K₂ →+* Ω), spMap i₁ ≫ a = spMap i₂ ≫ b := by
  intro X K₁ K₂ _ _ a b h
  obtain ⟨⟨x, f⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₁ X).symm.surjective a
  obtain ⟨⟨y, g⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₂ X).symm.surjective b
  have hxy : x = y := by
    have h1 := congrArg Sigma.fst ((Scheme.SpecToEquivOfField K₁ X).apply_symm_apply ⟨x, f⟩)
    have h2 := congrArg Sigma.fst ((Scheme.SpecToEquivOfField K₂ X).apply_symm_apply ⟨y, g⟩)
    exact h1.symm.trans (h.trans h2)
  subst hxy
  letI : Algebra (X.residueField x) K₁ := f.hom.toAlgebra
  letI : Algebra (X.residueField x) K₂ := g.hom.toAlgebra
  haveI : Nontrivial (TensorProduct (X.residueField x) K₁ K₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct (X.residueField x) K₁ K₂)
  letI : Field ((TensorProduct (X.residueField x) K₁ K₂) ⧸ m) := Ideal.Quotient.field m
  refine ⟨(TensorProduct (X.residueField x) K₁ K₂) ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := X.residueField x) (A := K₁) (B := K₂)).toRingHom, ?_⟩
  change Spec.map _ ≫ Spec.map f ≫ X.fromSpecResidueField x = Spec.map _ ≫ Spec.map g ≫ X.fromSpecResidueField x
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext c
  change Ideal.Quotient.mk m (TensorProduct.tmul _ (algebraMap _ K₁ c) 1) = Ideal.Quotient.mk m (TensorProduct.tmul _ 1 (algebraMap _ K₂ c))
  congr 1
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenRangeEqInterPreimageEtaleUnivOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_range_eq_inter_preimage_etale_univOpen : ∀ (X B T Z : Scheme.{0}) (c : X ⟶ B) (j : T ⟶ B) (i : Z ⟶ X) (φ : Z ⟶ T), Etale c → IsPreimmersion j → UniversallyOpen φ → i ≫ c = φ ≫ j → ∃ W : X.Opens, Set.range i = (W : Set X) ∩ c ⁻¹' Set.range j := by
  first | exact @GlobalTheory.Mum.exists_opens_range_eq_of_etale | exact GlobalTheory.Mum.exists_opens_range_eq_of_etale | (intros; apply GlobalTheory.Mum.exists_opens_range_eq_of_etale <;> assumption)
end

