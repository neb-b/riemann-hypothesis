module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0424
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitAwayFromLevelProdNormalisedMatrixGaussSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.GaussUnit

theorem isIntegral_of_eq {x y : ℂ} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

theorem unitOff_of_two {N : ℕ} {u : ℂ} (h0 : u ≠ 0) {a b : ℕ} (ha : IsIntegral ℤ ((N : ℂ) ^ a * u))
    (hb : IsIntegral ℤ ((N : ℂ) ^ b * u⁻¹)) : UnitOff N u := by
  have hN : ∀ c : ℕ, IsIntegral ℤ ((N : ℂ) ^ c) := fun c => by
    have : IsIntegral ℤ ((N : ℕ) : ℂ) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ)))
    exact this.pow c
  refine ⟨h0, a + b, ?_, ?_⟩
  · have := (hN b).mul ha
    refine isIntegral_of_eq (this) ?_
    ring
  · have := (hN a).mul hb
    refine isIntegral_of_eq (this) ?_
    ring

theorem unitOff_one (N : ℕ) : UnitOff N 1 :=
  unitOff_of_two (a := 0) (b := 0) one_ne_zero (by simpa using isIntegral_one) (by simpa using isIntegral_one)

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, a, ha, ha'⟩ := hu
  obtain ⟨hv0, b, hb, hb'⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, a + b, ?_, ?_⟩
  · refine isIntegral_of_eq (ha.mul hb) ?_
    ring
  · refine isIntegral_of_eq (ha'.mul hb') ?_
    rw [mul_inv]
    ring

theorem unitOff_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) :=
  Finset.prod_induction f (UnitOff N) (fun _ _ => unitOff_mul) (unitOff_one N) h

theorem unitOff_normalised {N q n r : ℕ} (hq : q ≠ 0) {m : ℕ} (hd : q ∣ N ^ m) (hrn : r ≤ n) {S : ℂ}
    (h1 : ‖S‖ ^ 2 = (q : ℝ) ^ (r ^ 2)) (h2 : IsIntegral ℤ S) (h3 : IsIntegral ℤ ((q : ℂ) ^ (r ^ 2) * S⁻¹)) :
    UnitOff N (((q : ℂ) ^ (n * r))⁻¹ * S) := by
  have hI : ∀ c : ℕ, IsIntegral ℤ ((c : ℕ) : ℂ) := fun c => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (c : ℤ)))
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hS : S ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < (q : ℝ) ^ (r ^ 2) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq) _
    rw [← h1] at this
    simp at this
  obtain ⟨c, hc⟩ := hd
  have hcC : (N : ℂ) ^ m = q * c := by exact_mod_cast hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrn
  refine unitOff_of_two (a := m * ((r + d) * r)) (b := 0) (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hqC)) hS) ?_ ?_
  · refine isIntegral_of_eq (((hI c).pow ((r + d) * r)).mul h2) ?_
    rw [pow_mul, hcC, mul_pow]
    field_simp
  · refine isIntegral_of_eq (((hI q).pow (d * r)).mul h3) ?_
    rw [mul_inv, inv_inv]
    ring

theorem card_dvd_pow (k : Type) [Field k] [Fintype k] {N : ℕ} (hN : (N : k) = 0) : ∃ m, Fintype.card k ∣ N ^ m := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨m, -, hm⟩ := FiniteField.card k p
  exact ⟨m, hm ▸ pow_dvd_pow_of_dvd ((CharP.cast_eq_zero_iff k p N).mp hN) _⟩

theorem unitOff_prod_gaussSum : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → UnitOff N (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) := by
  intro D _ Q n r hrn ψP ξ hψ hξ N _ hN
  refine unitOff_prod _ _ ?_
  rintro ⟨PP, hPP⟩ -
  haveI := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have h0 : (N : kP PP) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr (hN PP hPP)
    simpa using this
  obtain ⟨m, hm⟩ := card_dvd_pow (kP PP) h0
  obtain ⟨h1, h2, h3, -⟩ := _root_.GlobalTheory.complexMatrixGaussSum_norm_integral_galois (kP PP) (ψP PP) (ξ PP) r (hψ PP hPP) (hξ PP hPP) _ rfl
  rw [Nat.card_eq_fintype_card]
  exact unitOff_normalised Fintype.card_ne_zero hm hrn h1 h2 h3

end GlobalTheory.GaussUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFactorDepthEqSumFactorDepths
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IsoFactorDepth


open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns in
def colEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (cx : Lt1 Dw → ℕ) : Col cx ↪ (Σ f : Lt1 Dw, Fin (rk f)) where
  toFun b := ⟨b.1.1, b.2⟩
  inj' := by
    rintro ⟨⟨f, hf⟩, a⟩ ⟨⟨g, hg⟩, b⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    cases h
    rfl


open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns in
theorem prodP_eq_rename_polyH {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (C : Type) [Field C] (cx : Lt1 Dw → ℕ) :
    prodP C cx = MvPolynomial.rename (fun x : Let cx =>
      (⟨colEmb cx x.1, x.2⟩ : Σ b : (Σ f : Lt1 Dw, Fin (rk f)), Fin (rk b.1))) (polyH C cx) := by
  classical
  unfold prodP polyH
  rw [map_prod]
  simp_rw [MvPolynomial.rename_rename]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun f : Lt1 Dw => cx f ≠ 0)]
  have h1 : ∏ f : {f : Lt1 Dw // ¬ cx f ≠ 0}, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (rk f.1), Fin (rk f.1)) =>
      (⟨⟨f.1, ℓ.1⟩, ℓ.2⟩ : Σ b : (Σ f : Lt1 Dw, Fin (rk f)), Fin (rk b.1))) (GlobalTheory.FGDepth.detPow C (rk f.1) (cx f.1)) = 1 := by
    refine Finset.prod_eq_one fun f _ => ?_
    have h0 : cx f.1 = 0 := not_not.1 f.2
    rw [GlobalTheory.FGDepth.detPow, h0, pow_zero, map_one]
  rw [h1, mul_one]
  rfl

theorem nuH_vp_eq_nuP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx = nuP p y cx ∧ 0 ≤ nuP p y cx ∧ nuP p y cx ≠ ⊤ := by
  intro E _ _ _ H Dw l Xo c
  classical
  letI := H.starRing
  intro p _ T io y Ch X cx
  have hfac := (GlobalTheory.T.detFactorDepth_eq_chart_value_and_sum E H Dw l Xo c p T io y Ch X).1
  have hsum : nuP p y cx = ∑ f, nuFacC Ch X f (cx f) :=
    Finset.sum_congr rfl fun f _ => hfac f (cx f)
  have hbd : ∀ f, 0 ≤ nuFacC Ch X f (cx f) ∧
      nuFacC Ch X f (cx f) ≤ ((((rk f * cx f : ℕ) : ℝ) / (p - 1) : ℝ) : EReal) := fun f => by
    have h := _root_.GlobalTheory.FGDepth.detDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) (chD Ch.ch) (cx f) (fgl Ch X)
      (frame Ch X f) (isSatFrame_frame Ch X f)
    refine ⟨h.1, h.2.2.trans (le_of_eq ?_)⟩
    push_cast; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum, ← GlobalTheory.FactorDepthProd.nuProdC_eq_sum]
    unfold nuProdC GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp
    rw [prodP_eq_rename_polyH]
    exact (GlobalTheory.FGDepth.depth_restrict X.C (vX_vp X) (Σ f : Lt1 Dw, Fin (rk f)) (fun _ => chD Ch.ch)
      (fun _ => fgl Ch X) (fun b => Fin (rk b.1)) (fun b => frame Ch X b.1) (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx)
      (colEmb cx) (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx)).symm
  · rw [hsum]
    exact Finset.sum_nonneg fun f _ => (hbd f).1
  · rw [hsum]
    have hreal : ∃ r : ℝ, ∑ f, nuFacC Ch X f (cx f) = (r : EReal) := by
      refine Finset.sum_induction _ (fun x : EReal => ∃ r : ℝ, x = r) ?_ ⟨0, rfl⟩ ?_
      · rintro a b ⟨r, rfl⟩ ⟨s, rfl⟩
        exact ⟨r + s, (EReal.coe_add r s).symm⟩
      · intro f _
        have h0 := (hbd f).1
        have h1 := (hbd f).2
        refine ⟨(nuFacC Ch X f (cx f)).toReal, (EReal.coe_toReal ?_ ?_).symm⟩
        · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
        · exact ne_bot_of_le_ne_bot (by simp) h0
    obtain ⟨r, hr⟩ := hreal
    rw [hr]
    exact EReal.coe_ne_top r

end GlobalTheory.IsoFactorDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingOfNadelPairs
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Cartier GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NadelApp

theorem isIso_idealModuleι_of_forall_notMem {X : Scheme.{0}} (I : X.IdealSheafData)
    (h : ∀ x, x ∉ I.support) : IsIso (idealModuleι I) := by
  have h0 : toSubscheme I = 0 := by
    haveI : IsEmpty I.subscheme := ⟨fun z => h _ (I.range_subschemeι.le ⟨z, rfl⟩)⟩
    ext V t
    have e : I.subschemeι ⁻¹ᵁ V = ⊥ := eq_bot_iff.2 fun z _ => isEmptyElim z
    have : Subsingleton Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) := by
      rw [e]
      infer_instance
    exact this.elim _ _
  exact kernel.ι_of_zero h0

theorem qWeil_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (m : ℕ) :
    qWeil (0 : CartierDiv X) m = 0 := by
  funext z
  have : (0 : CartierDiv X).mult z = 0 := by
    rw [(CartierDiv.isEqn_zero z).mult_eq]
    by_cases hz : Order.coheight z = 1
    · exact (Scheme.ord_eq_iff hz one_ne_zero).2 (by simp)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _
  simp [qWeil, this]

theorem kawamataViehweg_complex : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → IsIntegral X → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef ℂ N) → (letI := algebraΓOfHom p; IsBig ℂ N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  intro hN X p D _ hproj _ K N hnef hbig q hq
  letI := algebraΓOfHom p
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj
  obtain ⟨J, hJ, hv⟩ := nadel_canonical_add hN X p D hproj K N N hnef.isLB 0 1 1 one_pos one_pos
    CartierDiv.eff_zero hnef hbig (fun C _ => by
      rw [interNumRed_one_eq_zero (isLB_toLB 0) (by rw [← toPic_apply, map_zero])]
      simp)
  haveI := isIso_idealModuleι_of_forall_notMem J fun x hx => (hJ x).1 hx (by
    rw [qWeil_zero]
    exact kltAt_zero_of_smooth (topologicalKrullDim_eq_of_smooth X p D) x)
  exact @Function.Injective.subsingleton _ _ _ (cohOn.mapIso Γ(X, ⊤) ⊤ q
    ((twistFunctor (tens K.bundle N)).mapIso (asIso (idealModuleι J)))).symm.injective (hv q hq)

end GlobalTheory.NadelApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTraceAlgebraicAtLowestTypes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.BigTop GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical

namespace GlobalTheory.TraceRatPf

theorem zero_of_span' {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ j, AddCommGroup (L j)] [∀ j, Module ℂ (L j)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (F : (∀ j, L j) →ₘₗ[ℂ] X) (v₀ : ∀ j, L j) (P : ∀ j, L j → Prop)
    (hspan : ∀ j, Submodule.span ℂ {u | P j u} = ⊤)
    (hstep : ∀ (v : ∀ j, L j) (j : ι) (u : L j), v j = v₀ j → P j u → F v = 0 → F (Function.update v j u) = 0)
    (h0 : F v₀ = 0) : ∀ v, F v = 0 := by
  have key : ∀ s : Finset ι, ∀ v : ∀ j, L j, (∀ j ∉ s, v j = v₀ j) → F v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have : v = v₀ := funext fun j => hv j (Finset.notMem_empty j)
      rw [this]; exact h0
    | insert a s ha ih =>
      intro v hv
      have h1 : F (Function.update v a (v₀ a)) = 0 := ih _ fun j hj => by
        by_cases hja : j = a
        · subst hja; simp
        · rw [Function.update_of_ne hja]; exact hv j (by simp [hja, hj])
      have hmem : v a ∈ Submodule.span ℂ {u | P a u} := by rw [hspan a]; trivial
      have hall : ∀ u ∈ Submodule.span ℂ {u | P a u},
          F (Function.update (Function.update v a (v₀ a)) a u) = 0 := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu => exact hstep _ a u (by simp) hu h1
        | zero => exact F.map_update_zero _ _
        | add x y _ _ hx hy => rw [F.map_update_add, hx, hy, add_zero]
        | smul c x _ hx => rw [F.map_update_smul, hx, smul_zero]
      have e : Function.update (Function.update v a (v₀ a)) a (v a) = v := by simp
      rw [← e]; exact hall _ hmem
  exact fun v => key Finset.univ v (fun j hj => absurd (Finset.mem_univ j) hj)

theorem adForm_lowT_equiv' {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hHW : R.models_HW) (i : Fin D.R.m) (x : Fin (R.nW i) → D.what₂.LL) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (hk : k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ)) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ) (hu : ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ)) : adForm R i x (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (adForm R i x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) := by
  have hmem : adForm R i x ∈ R.Wall i (sg0 D A) := by
    rw [← (hHW i (sg0 D A)).2.1]
    exact LinearMap.mem_range_self _ _
  have hfr : IsUnit ((R.MW i (sg0 D A)).fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ)
  have e1 : (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hfr
  have hkJ : kᴴ * Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) * k = Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) := by
    have hu1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have hg : ((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ) := by
    show _ = _
    rw [← (R.MW i (sg0 D A)).fr_gram τ]
    have e3 : (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ * ((R.MW i (sg0 D A)).fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ, e3, Matrix.one_mul,
      ← Matrix.mul_assoc ((R.MW i (sg0 D A)).fr τ) (((R.MW i (sg0 D A)).fr τ)⁻¹), e1, Matrix.one_mul]
    rw [← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc (kᴴ * _), hkJ]
  have hrep : (R.MW i (sg0 D A)).rep τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ) =
      (R.MW i (sg0 D A)).σ τ k := by
    unfold Formalism.IndefR.Mult.DSModel.rep
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, e1, Matrix.mul_one]
  have hupd : (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) =
      Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ) := by
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  rw [hupd]
  suffices H : ∀ T ∈ R.Wall i (sg0 D A), T (Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ)) =
      Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
        (T (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) from H _ hmem
  intro T0 hT0
  induction hT0 using Submodule.span_induction with
  | mem T hT =>
    exact hT.equiv τ _ hg _ _ (by rw [hrep]; exact hu)
  | zero => rfl
  | add S T _ _ hS hT =>
    simp only [MultilinearMap.add_apply, hS, hT]
    rfl
  | smul a T _ hT =>
    simp only [MultilinearMap.smul_apply, hT]
    rfl

end GlobalTheory.TraceRatPf

namespace GlobalTheory.TraceRatPf

theorem translate_all {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hcore : GlobalTheory.Hk3.Core R F) (hU : R.LUnif) (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec)
    (hext : IsExtVec (R.MW i (sg0 D A)) v₀) {ξ χ ξR Q ω φ} (hker : KerDat R i ξ χ ξR Q ω φ)
    (h : GA D (Vc D i)) (y : (R.cV i).W) (u : ∀ τ, lowT (R.MW i (sg0 D A)) τ)
    (hu : ∀ τ, (u τ : (R.MW i (sg0 D A)).sm τ) = v₀ τ) (x : Fin (R.nW i) → D.what₂.LL)
    (hx : adForm R i x (fun τ => u τ) = singleSeries R i ω φ h y u) (g : G) :
    ∀ v : ∀ τ, lowT (R.MW i (sg0 D A)) τ, adForm R i ((R.FW i).ρ g x) (fun τ => v τ) =
      D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) •
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (singleSeries R i ω φ h y v) := by
  have hs0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK (sg0 D A) :=
    fun x _ => congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) hs0
  have hc : (sg0 D A) (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) :=
    congrArg (fun s : D.what₂.LL →+* ℂ => s (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) hs0
  let Lin : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun t g' => Datum.thetaKO ω h g' (Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
        (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i t y))
      map_add' := fun a b => by funext g'; simp [Datum.thetaKO, map_add (f := _)]
      map_smul' := fun a b => by funext g'; simp [Datum.thetaKO, map_smul] }
  let act := Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)
  let c : ℂ := D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)
  let Rt : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) →ₘₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    (c • (act ∘ₗ Lin)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  let Lf : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) →ₘₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    (adForm R i ((R.FW i).ρ g x)).compLinearMap fun ρ => (lowT (R.MW i (sg0 D A)) ρ).subtype
  have hRt : ∀ w, Rt w = c • act (singleSeries R i ω φ h y w) := fun w => rfl
  have hLf : ∀ w, Lf w = adForm R i ((R.FW i).ρ g x) (fun ρ => (w ρ : (R.MW i (sg0 D A)).sm ρ)) := fun w => rfl
  have hrs : ∀ (g' : GA D (Wc D i)) (a b : GA D (Wc D i) → ℂ) (s : ℂ),
      Formalism.L2.Theta.rTr (Wc D i) g' a - s • Formalism.L2.Theta.rTr (Wc D i) g' b = Formalism.L2.Theta.rTr (Wc D i) g' (a - s • b) :=
    fun _ _ _ _ => rfl
  have hat : Lf u = Rt u := by
    rw [hLf, hRt]
    have e := congrArg (fun T => T (fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ))) ((hU i (sg0 D A)).2.2 g x)
    change adForm R i ((R.FW i).ρ g x) _ = _ at e
    rw [e, hc]
    change c • act (adForm R i x (fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ))) = _
    rw [hx]
  have key := zero_of_span' (Lf - Rt) u
    (fun ρ z => ∃ k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ),
      ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((v₀ ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ))
    (fun ρ => GlobalTheory.LowSpan.span_translates_eq_top _ _ hext ρ
      ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hσ)).2 ρ))
    (fun w ρ z hw ⟨k, hk, hu'⟩ h0 => by
      have hu2 : ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((w ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) := by
        rw [hu', hw, hu]
      have e1 := adForm_lowT_equiv' R hcore.models.HW i ((R.FW i).ρ g x) ρ k hk w z hu2
      have e2 := GlobalTheory.SeriesKEquiv.singleSeries_kEquiv R F hcore i _ χ ξR _ ω φ hker _ _ φ hker.vecOf h y g ρ k hk w z hu2
      rw [MultilinearMap.sub_apply, hLf, hRt, e1, e2]
      change Formalism.L2.Theta.rTr (Wc D i) _ (Lf w) - c • Formalism.L2.Theta.rTr (Wc D i) _ (act _) = 0
      rw [hrs, ← hRt, ← MultilinearMap.sub_apply, h0]
      rfl)
    (by rw [MultilinearMap.sub_apply, hat, sub_self])
  intro w
  have := key w
  rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt] at this
  exact this

end GlobalTheory.TraceRatPf

namespace GlobalTheory.TraceRatPf

theorem adForm_sum {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {ι : Type} (s : Finset ι) (f : ι → Fin (R.nW i) → D.what₂.LL) :
    adForm R i (∑ g ∈ s, f g) = ∑ g ∈ s, adForm R i (f g) := by
  induction s using Finset.induction_on with
  | empty =>
    have e := GlobalTheory.TraceClassRank.adForm_smul (R := R) (i := i) 0 0
    rw [zero_smul, map_zero, zero_smul] at e
    simpa using e
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.TraceClassRank.adForm_add, ih]

theorem traceRat : TraceRat := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hcore hU i v₀ hext ξ χ ξR Q ω φ hker U ψ h y u hu x hx
  let c' : G → D.what₂.LL := fun g =>
    if hg : g ∈ U then (((ψ ⟨g, hg⟩)⁻¹ * ((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0
  refine ⟨∑ g, c' g • (R.FW i).ρ g x, fun v => ?_⟩
  rw [adForm_sum, MultilinearMap.sum_apply]
  unfold levelTrace gaL
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [GlobalTheory.TraceClassRank.adForm_smul, MultilinearMap.smul_apply,
    translate_all R F hcore hU i v₀ hext hker h y u hu x hx g v, LinearMap.smul_apply, smul_smul, ← map_mul]
  congr 2
  by_cases hg : g ∈ U
  · simp only [c', dif_pos hg]
    rw [← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]
  · simp only [c', dif_neg hg, zero_mul, map_zero]

end GlobalTheory.TraceRatPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalActionLinearInVector
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocOpLin

theorem acts_lin : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)) (Op : Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ)
    (φ φ' η η' ζ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → φ' ∈ SB (κ → Fv F v) →
    Acts (evFin F v) Op φ η → Acts (evFin F v) Op φ' η' → Acts (evFin F v) Op (c • φ + φ') ζ → ζ = c • η + η' := by
  intro F _ _ κ _ v Op c φ φ' η η' ζ hφ hφ' h₁ h₂ h₃
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  have hs : c • φ + φ' ∈ SB (κ → Fv F v) := add_mem ((SB _).smul_mem c hφ) hφ'
  have e : ∀ α β : (κ → Fv F v) → ℂ, tens (evFin F v) (c • α + β) R =
      c • tens (evFin F v) α R + tens (evFin F v) β R := by
    intro α β
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have key : tens (evFin F v) ζ R = tens (evFin F v) (c • η + η') R := by
    rw [← h₃ R (hR _ hs), e, map_add (f := _), map_smul, h₁ R (hR φ hφ), h₂ R (hR φ' hφ'), e]
  funext y
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := by
    intro u' hu'
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have hRz : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    simpa using (hR φ hφ).1 0 _ hz
  have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (y i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
  exact mul_right_cancel₀ hR0 this

end GlobalTheory.LocOpLin
end
end

