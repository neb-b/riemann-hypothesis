module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumProdNormLeOfProdNormLowerBound

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCharpolyKernelEqStableOrbitalIntegrals
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll

open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt (ratClass classKernel)

theorem classKernel_eq_sum {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (g : H) (f : G → ℂ)
    (x : G) (T : Finset H) (hT : ∀ δ, f (x⁻¹ * ι δ * x) ≠ 0 → δ ∈ T) :
    classKernel ι.range (ι g) f x = ∑ δ ∈ T, {δ | IsConj g δ}.indicator (fun δ => f (x⁻¹ * ι δ * x)) δ := by
  let e : {δ | IsConj g δ} → ratClass ι.range (ι g) := fun δ => ⟨ι δ, by
    obtain ⟨c, hc⟩ := isConj_iff.1 δ.2
    exact ⟨ι c⁻¹, ⟨_, rfl⟩, by rw [← hc]; simp⟩⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (hι (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, _, ⟨c, rfl⟩, rfl⟩
    exact ⟨⟨c⁻¹ * g * c, isConj_iff.2 ⟨c⁻¹, by simp⟩⟩, Subtype.ext (by simp [e])⟩
  rw [classKernel, ← (Equiv.ofBijective e he).tsum_eq fun δ => f (x⁻¹ * δ * x)]
  refine (tsum_subtype {δ | IsConj g δ} fun δ => f (x⁻¹ * ι δ * x)).trans (tsum_eq_sum fun δ hδ => ?_)
  by_contra h
  exact hδ (hT δ fun h0 => h (by simp [indicator, h0]))

theorem finsum_eq_sum_classKernel {G H I : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι)
    (p : H → Prop) (g : I → H) (hp : ∀ δ, p δ ↔ ∃ i, IsConj (g i) δ) (hg : ∀ i j, IsConj (g i) (g j) → i = j)
    (f : G → ℂ) (S : Finset I) (hS : ∀ i ∉ S, ∀ x, f (x⁻¹ * ι (g i) * x) = 0) (x : G)
    (hx : {δ | f (x⁻¹ * ι δ * x) ≠ 0}.Finite) :
    ∑ᶠ δ : {δ // p δ}, f (x⁻¹ * ι δ.1 * x) = ∑ i ∈ S, classKernel ι.range (ι (g i)) f x := by
  classical
  rw [Finset.sum_congr rfl fun i _ => classKernel_eq_sum ι hι (g i) f x hx.toFinset fun δ h => hx.mem_toFinset.2 h,
    Finset.sum_comm]
  refine (finsum_set_coe_eq_finsum_mem (f := fun δ => f (x⁻¹ * ι δ * x)) {δ | p δ}).trans ?_
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset (s := hx.toFinset) _ fun δ h => by
    simpa using fun h0 => h (by simp [indicator, h0])]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  by_cases h : p δ
  · obtain ⟨i, hi⟩ := (hp δ).1 h
    have hiS : i ∈ S := by
      by_contra hn
      obtain ⟨c, hc⟩ := isConj_iff.1 hi
      refine hx.mem_toFinset.1 hδ ?_
      rw [← hS i hn ((ι c)⁻¹ * x), ← hc]
      simp [mul_assoc]
    rw [indicator_of_mem (show δ ∈ {δ | p δ} from h), Finset.sum_eq_single_of_mem i hiS fun j _ hj =>
      indicator_of_notMem (s := {δ | IsConj (g j) δ}) (fun (hc : IsConj (g j) δ) => hj (hg j i (hc.trans hi.symm))) _,
      indicator_of_mem (show δ ∈ {δ | IsConj (g i) δ} from hi)]
  · rw [indicator_of_notMem (show δ ∉ {δ | p δ} from h), Finset.sum_eq_zero fun j _ =>
      indicator_of_notMem (s := {δ | IsConj (g j) δ}) (fun (hc : IsConj (g j) δ) => h ((hp δ).2 ⟨j, hc⟩)) _]

theorem classKernel_eq_zero {G : Type} [Group G] (Γ : Subgroup G) (γ : G) (f : G → ℂ) (h : ∀ x, f (x⁻¹ * γ * x) = 0) :
    classKernel Γ γ f = 0 := by
  funext x
  refine (tsum_congr ?_).trans tsum_zero
  rintro ⟨_, c, -, rfl⟩
  rw [← h (c * x)]
  simp [mul_assoc]

theorem finite_of_eventually_eq_one {V Y : Type} [Finite Y] {C : V → Type} [∀ v, One (C v)] [∀ v, Finite (C v)]
    {X : ∀ v, Set (C v)} {p : (∀ v, X v) × Y → Prop} (A : Set {q // p q})
    (h : ∀ᶠ v in cofinite, ∀ i ∈ A, (i.1.1 v).1 = 1) : A.Finite := by
  have : Finite {v | ¬ ∀ i ∈ A, (i.1.1 v).1 = 1} := eventually_cofinite.1 h
  refine Set.Finite.of_finite_image
    (f := fun i : {q // p q} => ((fun v : {v | ¬ ∀ i ∈ A, (i.1.1 v).1 = 1} => i.1.1 v), i.1.2)) (Set.toFinite _)
    fun i hi j hj e => Subtype.ext (Prod.ext (funext fun v => ?_) (congrArg Prod.snd e :))
  by_cases hv : ∀ i ∈ A, (i.1.1 v).1 = 1
  · exact Subtype.ext ((hv i hi).trans (hv j hj).symm)
  · exact congrFun (congrArg Prod.fst e) ⟨v, hv⟩

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
  {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}

theorem exists_isCompact_tensor (ha : ∀ w, HasCompactSupport (fa w)) (hf : IsFinFamily σ J L ff) :
    ∃ C, IsCompact C ∧ ∀ y, tensor σ J fa ff y ≠ 0 → y ∈ C := by
  refine ⟨_, (infFinEquiv σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (IsCompact.prod
    ((infContEquivPi σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi ha))
      hf.tensorFin_mem.2), fun y hy => ?_⟩
  rw [tensor_eq_infFin] at hy
  exact ⟨fun w _ => subset_tsupport _ (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hy) w (Finset.mem_univ w)),
    subset_tsupport _ (right_ne_zero_of_mul hy)⟩

theorem ne_zero_of_tensor (hf : IsFinFamily σ J L ff) {y : GAd σ J} (hy : tensor σ J fa ff y ≠ 0) (v) :
    ff v (proj σ J v y) ≠ 0 := by
  rw [tensor_eq_infFin] at hy
  simpa only [projFinLoc_projFin] using (hf.tensorFin_ne_zero_iff _).1 (right_ne_zero_of_mul hy) v


omit [NumberField F] [NumberField E] in
theorem charpoly_eq_of_isConj {γ δ : GRat σ J} (h : IsConj γ δ) : δ.1.1.charpoly = γ.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have : (c * γ * c⁻¹).1.1 = c.1.1 * γ.1.1 * (c.1⁻¹).1 := rfl
  rw [this, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end Adelic

theorem integral_polKernel : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → Integrable (descend (ratPts σ J) (polKernel P J (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf v) (ff v)) * ∏ w, Phi (J := J) (μa w) (dta w) (fa w) := by
  classical
  intro E _ _ F _ σ hCM hun r P J hJ L _ μa μf μ hμ fa ff hfa hff dta dtf dt hdt
  obtain ⟨H1, H2, H3⟩ := GlobalTheory.T.rational_unitary_classes_iff_local_class_families E F σ hCM hun r P J hJ
  obtain ⟨Ff, Fa⟩ := _root_.GlobalTheory.SqCls.finite_cls F E σ hCM r P
  have hae := _root_.GlobalTheory.TrEll.eventually_unitLoc_orbCls F E σ hCM r P J hJ L
  have hcl := GlobalTheory.T.rationalClassTerm_eq_volume_mul_prod_orbitalIntegrals F E σ hCM r P J hJ L μa μf μ hμ fa ff hfa hff dta dtf dt hdt
  let I := {p : (∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) × (∀ w : InfinitePlace F, XSet P w.Completion J) //
    ∀ᶠ v in cofinite, (p.1 v).1 = 1}
  obtain ⟨hsupp, hsum⟩ := finsum_restrictedFamily_eq_prod_finsum (HeightOneSpectrum (𝓞 F)) (InfinitePlace F)
    (fun v => Cls P (Fv F v)) (fun v => XSet P (Fv F v) J) (fun w => XSet P w.Completion J) (fun v => Set.toFinite _)
    (fun v => orbCls (μf v) (dtf v) (ff v)) (fun w => orbCls (μa w) (dta w) (fa w)) (by
      filter_upwards [hae, hff.2, hμ.eventually_eq_one, IsRestrictedProd.eventually_eq_one hdt] with v h1 h2 h3 h4
      rw [h2]
      exact ⟨h1.1, h1.2.2.2 _ _ (hμ.haar_loc v) (IsRestrictedProd.haar_loc hdt v) h3 h4⟩)
  choose g g1 g2 g3 using fun i : I => H3 (fun v => (i.1.1 v).1) (fun w => (i.1.2 w).1) (fun v => (i.1.1 v).2)
    (fun w => (i.1.2 w).2) i.2
  have hp : ∀ δ : GRat σ J, δ.1.1.charpoly = P.1 ↔ ∃ i, IsConj (g i) δ := fun δ => by
    refine ⟨fun h => ?_, fun ⟨i, hi⟩ => (charpoly_eq_of_isConj hi).trans (g1 i)⟩
    obtain ⟨a1, a2, a3⟩ := H1 δ h
    choose qf qf1 qf2 using a1
    choose qa qa1 qa2 using a2
    let i : I := ⟨(fun v => ⟨qf v, (qf1 v).mem⟩, fun w => ⟨qa w, (qa1 w).mem⟩), a3.mono fun v hv => (qf2 v 1 hv).symm⟩
    refine ⟨i, IsConj.symm ((H2 δ (g i) h (g1 i)).2 ⟨fun v q hq => ?_, fun w q hq => ?_⟩)⟩
    · rw [qf2 v q hq]; exact g2 i v
    · rw [qa2 w q hq]; exact g3 i w
  have hg : ∀ i j, IsConj (g i) (g j) → i = j := fun i j h => by
    obtain ⟨b1, b2⟩ := (H2 _ _ (g1 i) (g1 j)).1 h
    obtain ⟨a1, a2, -⟩ := H1 _ (g1 j)
    have e1 : ∀ v, i.1.1 v = j.1.1 v := fun v => Subtype.ext ((a1 v).unique (b1 v _ (g2 i v)) (g2 j v))
    have e2 : ∀ w, i.1.2 w = j.1.2 w := fun w => Subtype.ext ((a2 w).unique (b2 w _ (g3 i w)) (g3 j w))
    exact Subtype.ext (Prod.ext (funext e1) (funext e2))
  have hfin : {i : I | ∃ x, tensor σ J fa ff (x⁻¹ * ratEmb σ J (g i) * x) ≠ 0}.Finite := by
    refine finite_of_eventually_eq_one _ ?_
    filter_upwards [hae, hff.2] with v h1 h2
    rintro i ⟨x, hx⟩
    have h3 := ne_zero_of_tensor hff hx v
    rw [h2, map_mul, map_mul, map_inv] at h3
    exact h1.2.1 _ _ (g2 i v) ⟨_, by_contra fun hn => h3 (indicator_of_notMem hn _)⟩
  have hS : ∀ i ∉ hfin.toFinset, ∀ x, tensor σ J fa ff (x⁻¹ * ratEmb σ J (g i) * x) = 0 := fun i hi x =>
    by_contra fun h => hi (hfin.mem_toFinset.2 ⟨x, h⟩)
  obtain ⟨C, hC, hC'⟩ := exists_isCompact_tensor (fun w => (hfa w).2) hff
  have hker0 : ∀ x, polKernel P J (tensor σ J fa ff) x = ∑ i ∈ hfin.toFinset,
      classKernel (ratPts σ J) (ratEmb σ J (g i)) (tensor σ J fa ff) x := fun x => by
    rw [polKernel, ← range_ratEmb]
    exact finsum_eq_sum_classKernel (ratEmb σ J) (ratEmb_injective σ J) _ g hp hg _ _ hS x
      (((GlobalTheory.TrFinite.finite_charpoly_and_ratPts F E σ hCM r J C hC).2 x).subset fun δ h => hC' _ h)
  have hker : descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) = fun q => ∑ i ∈ hfin.toFinset,
      descend (ratPts σ J) (classKernel (ratPts σ J) (ratEmb σ J (g i)) (tensor σ J fa ff)) q := by
    funext q
    simp only [descend, hker0]
  have hi := fun i : I => hcl (g i) (g1 i) i.1.1 i.1.2 (g2 i) (g3 i)
  rw [hker]
  refine ⟨integrable_finsetSum _ fun i _ => (hi i).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hi i).1, Finset.sum_congr rfl fun i _ => (hi i).2, mul_assoc]
  simp only [Phi]
  rw [← hsum, mul_finsum' _ _ hsupp]
  refine (finsum_eq_sum_of_support_subset _ fun i hn => ?_).symm
  by_contra h
  refine hn ((hi i).2.symm.trans ?_)
  rw [classKernel_eq_zero _ _ _ (hS i h)]
  simp only [descend, Pi.zero_apply, integral_zero]

end GlobalTheory.TrEll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFiniteHeisenbergCombination
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CombTheta

theorem comb_theta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (g : WO S T → ℂ), IsThetaFunO ψ S T g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsThetaFunO ψ S T (∑ z ∈ R, c z • heisO ψ S T (t z) g) ∧ ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ R, c z • heisO ψ S T (t z) g) φ = ∑ z ∈ R, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  classical
  intro D ψ θ S T hψ hθ g hg ι R c t ht
  have ft := GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ g hg
  have hth : ∀ z ∈ R, IsThetaFunO ψ S T (heisO ψ S T (t z) g) := fun z hz => (ft.2 (t z) (ht z hz)).1
  have key : ∀ s ⊆ R, IsThetaFunO ψ S T (∑ z ∈ s, c z • heisO ψ S T (t z) g) ∧
      ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
        (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ),
        pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ s, c z • heisO ψ S T (t z) g) φ =
          ∑ z ∈ s, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ⟨GlobalTheory.OrientedHeis.theta_zero, fun sS BS sT BT φ =>
        GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
    | insert i s hi ih =>
      intro hs
      have hiR : i ∈ R := hs (Finset.mem_insert_self i s)
      have ih' := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
      simp only [Finset.sum_insert hi]
      refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hth i hiR)) ih'.1, fun sS BS sT BT φ => ?_⟩
      rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (c i) (hth i hiR) ih'.1 φ, ih'.2,
        (ft.2 (t i) (ht i hiR)).2 sS BS sT BT φ]
  exact ⟨(key R subset_rfl).1, fun sS BS sT BT φ => (key R subset_rfl).2 sS BS sT BT φ⟩

end GlobalTheory.CombTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockLatVac

theorem infPart_latO_any {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add (f := _), hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem theta_isLatVac_pureTensorO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T LS LT P) g → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) ∧ IsLatVac (heisO ψ S T) (latO S T LS LT P) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  intro D ψ θ S T hψ hθ LS LT P g hg hvac sS BS sT BT φ
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) := fun φ =>
    GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ sS BS sT BT hg φ
  refine ⟨hth φ, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hθ sS sT BS BT g hth (2 • u)
      (infPart_latO_any (AddSubgroup.nsmul_mem _ hu 2)) (hvac.1 u hu) φ
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hθ sS sT BS BT g hth u
      (infPart_latO_any hu) (hvac.2 e he u hu hh) φ

end GlobalTheory.FockLatVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanChangesByScalarOfTrivialAction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IsoMean

theorem GlobalTheory.IsoMean.meanX_prod_zero : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (ratMx D a b) μ 𝓨 → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (GlobalTheory.IsoMean.emb V W P Q y) = GlobalTheory.IsoMean.emb V W P Q y) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ y : Mx D a b, actO V W g h x = x + GlobalTheory.IsoMean.emb V W P Q y) → ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 (ω (g, h) f) 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 (ω (g, h) f') 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 f 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 f' 0) := by
  intro D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip f f' hf hf'
  exact GlobalTheory.T.isotropicIntegrals_determine_thetaMean_products D V W a b P Q hP hQ hiso ψ hω.std μ 𝓨 hμ _ _ _ _ (hω.om_pres _ f hf) (hω.om_pres _ f' hf') hf hf'
    (fun ν 𝓕 hν h𝓕 w hw => GlobalTheory.IsoMean.coef_integral_eq D V W a b P Q ψ χS χT ω hω μ hμ.1 g h hfix hunip ν 𝓕 hν h𝓕 f f'
      hf hf' w hw)

namespace GlobalTheory.IsoMean

theorem mean_scalar : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (HMul.hMul (HMul.hMul (P.map (incA D)) (y' : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (ratMx D a b) μ 𝓨 → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∃ y : Mx D a b, actO V W g h x = x + (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → ∃ c : Circle, ∀ f, IsThetaFunO ψ V W f → ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∫ y in 𝓨, heisO ψ V W x (ω (g, h) f) (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = (c : ℂ) * ∫ y in 𝓨, heisO ψ V W x f (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  intro D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip
  change ∀ y y' : Mx D a b, symplO V W (emb V W P Q y) (emb V W P Q y') = 0 at hiso
  change ∀ y : Mx D a b, actO V W g h (emb V W P Q y) = emb V W P Q y at hfix
  change ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (emb V W P Q y) = 0) →
    ∃ y : Mx D a b, actO V W g h x = x + emb V W P Q y at hunip
  have hψ := hω.std
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e

  have phase : ∀ x, (∀ y, symplO V W x (emb V W P Q y) = 0) → ∀ y₀ y,
      symplOH V W (emb V W P Q y) (x + emb V W P Q y₀) = 0 := fun x hx y₀ y => by
    rw [l2, skew, hH _ _ (hx y), hH _ _ (hiso y y₀), neg_zero, add_zero]

  have hint : ∀ (F : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      ∫ y in 𝓨, heisO ψ V W x F (emb V W P Q y) ∂μ = meanX V W P Q μ 𝓨 F x := fun F x hx => by
    unfold meanX heisO
    congr 1; funext y
    have := phase x hx 0 y
    rw [show emb V W P Q (0 : Mx D a b) = 0 by simp [emb], add_zero] at this
    rw [this, AddChar.map_zero_eq_one, one_mul]
  have hmean : ∀ (F : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) → ∀ y₀,
      meanX V W P Q μ 𝓨 (heisO ψ V W (x + emb V W P Q y₀) F) 0 = meanX V W P Q μ 𝓨 F (x + emb V W P Q y₀) :=
    fun F x hx y₀ => by
      unfold meanX heisO
      congr 1; funext y
      rw [add_zero, phase x hx y₀ y, AddChar.map_zero_eq_one, one_mul]
  have hz : emb V W P Q (0 : Mx D a b) = 0 := by simp [emb]

  have hωx : ∀ f, IsThetaFunO ψ V W f → ∀ x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      meanX V W P Q μ 𝓨 (ω (g, h) (heisO ψ V W x f)) 0 = meanX V W P Q μ 𝓨 (ω (g, h) f) x := fun f hf x hx => by
    obtain ⟨y₀, hy₀⟩ := hunip x hx
    rw [hω.om_heis g h x f hf, hy₀, hmean _ x hx y₀, add_comm,
      GlobalTheory.IsoMean.meanX_translate D V W a b P Q hiso ψ hψ μ 𝓨 hμ _ (hω.om_pres _ f hf) x hx y₀]
  have hfx : ∀ (f : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      meanX V W P Q μ 𝓨 (heisO ψ V W x f) 0 = meanX V W P Q μ 𝓨 f x := fun f x hx => by
    have := hmean f x hx 0
    rwa [hz, add_zero] at this
  let Ix := {p : (WO V W → ℂ) × WO V W // IsThetaFunO ψ V W p.1 ∧ ∀ y, symplO V W p.2 (emb V W P Q y) = 0}
  obtain ⟨c, hc, hcf⟩ := GlobalTheory.ThetaCoefficient.exists_unit_smul (X := Ix)
    (fun p => meanX V W P Q μ 𝓨 p.1.1 p.1.2) (fun p => meanX V W P Q μ 𝓨 (ω (g, h) p.1.1) p.1.2)
    (fun p q => by
      have e := meanX_prod_zero D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip
        (heisO ψ V W q.1.2 q.1.1) (heisO ψ V W p.1.2 p.1.1)
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ q.2.1 _) (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ p.2.1 _)
      rwa [hωx _ q.2.1 _ q.2.2, hωx _ p.2.1 _ p.2.2, hfx _ _ q.2.2, hfx _ _ p.2.2] at e)
  refine ⟨⟨c, ?_⟩, fun f hf x hx => ?_⟩
  · show c ∈ Metric.sphere (0 : ℂ) 1
    exact mem_sphere_zero_iff_norm.2 hc
  · have e := congrFun hcf ⟨(f, x), hf, hx⟩
    simp only [Pi.smul_apply, smul_eq_mul] at e
    exact (hint (ω (g, h) f) x hx).trans (e.trans (congrArg _ (hint f x hx).symm))

end GlobalTheory.IsoMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumLongVectorsDecayWeightLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

variable {D : D7}

def compVec (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) :
    (Fin V.rank → D.host.E) →+ (D.what₂.Tau → EuclideanSpace ℂ (Fin V.rank)) where
  toFun w τ := WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (w i)))
  map_zero' := by
    funext τ
    have h : (fun i => tauE D τ ((0 : Fin V.rank → D.host.E) i)) = 0 := by
      funext i; simp
    show WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ ((0 : Fin V.rank → D.host.E) i))) = 0
    rw [h, Matrix.mulVec_zero, Matrix.mulVec_zero]
    rfl
  map_add' x y := by
    funext τ
    have h : (fun i => tauE D τ ((x + y) i)) = (fun i => tauE D τ (x i)) + fun i => tauE D τ (y i) := by
      funext i; simp
    show WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ ((x + y) i))) =
      WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (x i))) +
        WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (y i)))
    rw [h, Matrix.mulVec_add, Matrix.mulVec_add, WithLp.toLp_add]

theorem norm_compVec (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (w : Fin V.rank → D.host.E) (τ : D.what₂.Tau) :
    ‖compVec θ V B g w τ‖ = nrm θ B g τ w := by
  rw [EuclideanSpace.norm_eq]; rfl

theorem latSum_le : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (L : Lat V) (R : ℝ), 1 ≤ V.rank → 1 < R → (∀ w ∈ L, w ≠ 0 → R ≤ ∏ τ, nrm θ B g τ w) → ∀ s : Finset (Fin V.rank → D.host.E), (∀ w ∈ s, w ∈ L ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + nrm θ B g τ w) / 3) ^ (2 * V.rank + 5))⁻¹ ≤ Real.exp ((6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) / R := by
  intro D θ V B g L R hn hR hL s hs
  classical
  have hnorm : ∀ w τ, ‖compVec θ V B g w τ‖ = nrm θ B g τ w := norm_compVec θ V B g
  by_cases hι : IsEmpty D.what₂.Tau
  · have hs0 : s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      have h1 := hL w (hs w hw).1 (hs w hw).2
      rw [Finset.univ_eq_empty, Finset.prod_empty] at h1
      linarith
    subst hs0
    rw [Finset.sum_empty]
    exact div_nonneg (Real.exp_pos _).le (by linarith)
  · haveI : Nonempty D.what₂.Tau := not_isEmpty_iff.mp hι
    have hzero : ∀ w, compVec θ V B g w = 0 → ∏ τ, nrm θ B g τ w = 0 := by
      intro w h0
      refine Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _)) ?_
      rw [← hnorm, h0, Pi.zero_apply, norm_zero]
    have hinj : Set.InjOn (compVec θ V B g) (s : Set _) := by
      intro x hx y hy hxy
      by_contra hne
      have hm : x - y ∈ L := L.sub_mem (hs x hx).1 (hs y hy).1
      have h1 := hL _ hm (sub_ne_zero.mpr hne)
      have hz : compVec θ V B g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hzero _ hz] at h1
      linarith
    have key := _root_.GlobalTheory.ProdNormSum.lattice_sum_le D.what₂.Tau V.rank (L.toAddSubgroup.map (compVec θ V B g)) R hn hR ?_
      (s.image (compVec θ V B g)) ?_
    · rw [Finset.sum_image hinj] at key
      simpa only [hnorm] using key
    · intro v hv hv0
      obtain ⟨w, hwL, rfl⟩ := AddSubgroup.mem_map.mp hv
      have hwL' : w ∈ L := hwL
      have hw0 : w ≠ 0 := by rintro rfl; exact hv0 (map_zero _)
      simpa only [hnorm] using hL w hwL' hw0
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      refine ⟨AddSubgroup.mem_map_of_mem _ (hs w hw).1, ?_⟩
      intro h0
      have h1 := hL w (hs w hw).1 (hs w hw).2
      rw [hzero w h0] at h1
      linarith

end GlobalTheory.SepPer

end
end

