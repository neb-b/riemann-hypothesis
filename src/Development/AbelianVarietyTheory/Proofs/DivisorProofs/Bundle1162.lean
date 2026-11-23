module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTri
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EtaInfSign

open GlobalTheory.QuadSymbol

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem mem_normGroup_of_pos (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ)
    (hy : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion)) :
    y ∈ normGroup (maximalRealSubfield E) E v.Completion := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq (maximalRealSubfield E) E
  rw [mem_normGroup_iff_form b h0 h1]
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hy' : 0 < e y := hy
  refine ⟨e.symm (Real.sqrt (e y)), 0, e.injective ?_⟩
  simp only [map_sub, map_pow, map_mul, map_zero, RingEquiv.apply_symm_apply]
  rw [zero_pow two_ne_zero, mul_zero, sub_zero, Real.sq_sqrt hy'.le]

theorem not_mem_normGroup_of_neg (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ)
    (hy : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion) < 0) :
    y ∉ normGroup (maximalRealSubfield E) E v.Completion := by
  intro hmem
  have hneg : (-y) ∈ normGroup (maximalRealSubfield E) E v.Completion := by
    refine mem_normGroup_of_pos E v (-y) ?_
    rw [Units.val_neg, map_neg]
    exact neg_pos.2 hy
  have h1 : (-1 : (v.Completion)ˣ) ∈ normGroup (maximalRealSubfield E) E v.Completion := by
    have : (-1 : (v.Completion)ˣ) = y * (-y)⁻¹ := by
      rw [inv_neg, mul_neg, mul_inv_cancel]
    rw [this]
    exact mul_mem hmem (inv_mem hneg)
  exact eta_eq_neg_one_iff.1 (GlobalTheory.GalOfCusp.eta_neg_one E v) h1

theorem eta_real (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ) :
    eta (maximalRealSubfield E) E v.Completion y =
      if 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion)
      then 1 else -1 := by
  split_ifs with h
  · exact eta_eq_one_iff.2 (mem_normGroup_of_pos E v y h)
  · have h0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion) ≠ 0 :=
      fun h' => y.ne_zero ((InfinitePlace.Completion.extensionEmbeddingOfIsReal _).injective (h'.trans (map_zero _).symm))
    exact eta_eq_neg_one_iff.2 (not_mem_normGroup_of_neg E v y (lt_of_le_of_ne (not_lt.1 h) h0))

theorem embedding_comp_algebraMap (w : InfinitePlace E) :
    (w.comap (algebraMap (maximalRealSubfield E) E)).embedding =
      w.embedding.comp (algebraMap (maximalRealSubfield E) E) := by
  have hw : w.comap (algebraMap (maximalRealSubfield E) E) =
      InfinitePlace.mk (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) := by
    conv_lhs => rw [← InfinitePlace.mk_embedding w]
    rw [InfinitePlace.comap_mk]
  rw [hw]
  rcases InfinitePlace.embedding_mk_eq (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) with h | h
  · exact h
  · rw [h]
    exact ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal _)

theorem extensionEmbedding_completionMap (w : InfinitePlace E)
    (x : (w.comap (algebraMap (maximalRealSubfield E) E)).Completion) :
    InfinitePlace.Completion.extensionEmbedding w
      (AbsoluteValue.Completion.map (w.comap (algebraMap (maximalRealSubfield E) E)).1 w.1 x) =
    ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal _) x : ℝ) : ℂ) := by
  induction x using AbsoluteValue.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        (AbsoluteValue.Completion.continuous_map _ _))
      (Complex.continuous_ofReal.comp (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous)
  | ih a =>
    rw [AbsoluteValue.Completion.map_coe, InfinitePlace.Completion.extensionEmbedding_coe,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, InfinitePlace.embedding_of_isReal_apply,
      embedding_comp_algebraMap]
    rfl

theorem unitDir_ofReal (r : ℝ) (hr : r ≠ 0) (u : ℂˣ) (hu : (u : ℂ) = r) :
    GlobalTheory.ConsEta.unitDir u = Units.map (Int.castRingHom ℂ).toMonoidHom (if 0 < r then 1 else -1) := by
  ext
  change (u : ℂ) / (‖(u : ℂ)‖ : ℂ) = _
  rw [hu, Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_pos h, div_self (Complex.ofReal_ne_zero.2 hr)]
    simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hr), Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr)]
    simp

end GlobalTheory.EtaInfSign


open GlobalTheory.QuadSymbol in
theorem GlobalTheory.EtaInfSign.quadChar_eq_infSign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    (∀ v, (b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1) →
    (GlobalTheory.GalOfCusp.quadChar E).1 b = GlobalTheory.ConsEta.infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  intro E _ _ _ b hb
  have hfin : GlobalTheory.IdeleNormChar.finComp b = 1 := funext fun v => Units.ext (hb v)
  have hL : (GlobalTheory.GalOfCusp.quadChar E).1 b = Units.map (Int.castRingHom ℂ).toMonoidHom
      (∏ v : InfinitePlace (maximalRealSubfield E),
        eta (maximalRealSubfield E) E v.Completion (GlobalTheory.IdeleNormChar.infComp b v)) := by
    change Units.map _ (etaProd _ E (GlobalTheory.IdeleNormChar.finComp b) (GlobalTheory.IdeleNormChar.infComp b)) = _
    unfold etaProd
    rw [hfin]
    have h1 : (fun v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) =>
        eta (maximalRealSubfield E) E (v.adicCompletion _) ((1 : FinFam (maximalRealSubfield E)) v)) = fun _ => 1 :=
      funext fun v => eta_eq_one_iff.2 (one_mem _)
    rw [h1, finprod_one, one_mul]
  rw [hL, map_prod, GlobalTheory.ConsEta.infSign, MonoidHom.finsetProd_apply]
  symm
  refine Fintype.prod_equiv (IsCMField.equivInfinitePlace E) _ _ fun w => ?_
  rw [IsCMField.equivInfinitePlace_apply, GlobalTheory.EtaInfSign.eta_real]
  have hv := IsTotallyReal.isReal (w.comap (algebraMap (maximalRealSubfield E) E))
  refine GlobalTheory.EtaInfSign.unitDir_ofReal _ ?_ _ ?_
  · intro h'
    exact (GlobalTheory.IdeleNormChar.infComp b _).ne_zero
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective (by rw [map_zero]; exact h'))
  · exact GlobalTheory.EtaInfSign.extensionEmbedding_completionMap E w _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOne
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.Hartogs

theorem regAt_of_forall_dvr : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
    ∀ (φ : X.functionField) (x : X),
      (∀ z : X, z ⤳ x → IsDiscreteValuationRing (X.presheaf.stalk z) → RegAt z φ) → RegAt x φ := by
  intro X _ _ hN f x hreg
  by_contra hf
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI := isIntegrallyClosed_sections_of_stalks hN hU
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  have key : ∀ y : U, RegAt (y : X) f ↔ ∃ s c : Γ(X, U), algebraMap _ X.functionField s * f =
      algebraMap _ X.functionField c ∧ s ∉ (hU.primeIdealOf y).asIdeal := fun y =>
    haveI := hU.isLocalization_stalk y
    GlobalTheory.NormalPole.mem_range_iff (B := X.presheaf.stalk (y : X)) (hU.primeIdealOf y).asIdeal f
  obtain ⟨p, hp, hpQ, h1, hpf⟩ := GlobalTheory.NormalPole.exists_height_one f (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    fun s c e => by_contra fun hs => hf ((key ⟨x, hx⟩).2 ⟨s, c, e, hs⟩)
  let P : PrimeSpectrum Γ(X, U) := ⟨p, hp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ x := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hpQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
  have hfz : ¬ RegAt (z : X) f := fun h => by
    obtain ⟨s, c, e, hs⟩ := (key z).1 h
    rw [hP] at hs
    exact hs (hpf s c e)
  clear_value z
  haveI := hU.isLocalization_stalk z
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    isDiscreteValuationRing_of_height_eq_one (hU.primeIdealOf z).asIdeal (by rw [hP]; exact h1) _
  exact hfz (hreg z hzx inferInstance)

end GlobalTheory.Hartogs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexRestrictedProductComponentwiseEqProd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RelIdxRestr

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_iInf_comap {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v))
    (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (C H : ∀ v, Subgroup (Y v))
    (_hfin : ∀ v, (H v).relIndex (C v) ≠ 0) (hev : ∀ᶠ v in cofinite, C v ≤ H v) :
    (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  classical
  set S : Finset V := (Filter.eventually_cofinite.1 hev).toFinset with hS
  have hSm : ∀ v, v ∉ S → C v ≤ H v := fun v hv => by
    by_contra h; exact hv (by simpa [hS] using h)
  set Cg := ⨅ v, (C v).comap (pf v)
  set Hg := ⨅ v, (H v).comap (pf v)
  have hmemC : ∀ x : X, x ∈ Cg ↔ ∀ v, pf v x ∈ C v := fun x => by simp [Cg, Subgroup.mem_iInf]
  have hmemH : ∀ x : X, x ∈ Hg ↔ ∀ v, pf v x ∈ H v := fun x => by simp [Hg, Subgroup.mem_iInf]
  let φ : Cg →* ∀ v : S, C v := MonoidHom.pi fun v =>
    ((pf v).comp Cg.subtype).codRestrict (C v) fun x => (hmemC x).1 x.2 v
  have hφ : ∀ x (v : S), ((φ x v : C v) : Y v) = pf v x := fun _ _ => rfl
  have hsurj : Function.Surjective φ := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z
      (GlobalTheory.RestrMeas.eventually_of_finset S fun v hv => by simp [z, hv, one_mem])
    have hxC : x ∈ Cg := (hmemC x).2 fun v => by
      rw [hx v]
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    refine ⟨⟨x, hxC⟩, funext fun v => Subtype.ext ?_⟩
    rw [hφ]
    show pf v x = _
    rw [hx v]
    simp [z, v.2]
  have hcomap : Hg.subgroupOf Cg = (Subgroup.pi Set.univ fun v : S => (H v).subgroupOf (C v)).comap φ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, hmemH]
    constructor
    · intro h v; exact h v
    · intro h v
      by_cases hv : v ∈ S
      · exact h ⟨v, hv⟩
      · exact hSm v hv ((hmemC x).1 x.2 v)
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ,
    finprod_eq_prod_of_mulSupport_subset (s := S)]
  · exact (Finset.prod_coe_sort S fun v => (H v).relIndex (C v))
  · intro v hv
    by_contra h
    exact hv (Subgroup.relIndex_eq_one.2 (hSm v h))

end GlobalTheory.RelIdxRestr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.VolBr.RepDict

theorem exists_quot {X : Scheme.{0}} [IsIntegral X] {B : LB X} (hB : B.IsLB) {ρ : B.ι → X.functionFieldˣ}
    (hρ : IsRatSec B ρ) : ∃ e : B.Sec → X.functionField,
      ∀ u c (hc : genericPoint X ∈ B.U c), e u * (ρ c : X.functionField) = fnOf _ hc (u.f c) := by
  obtain ⟨c₀, h₀⟩ : ∃ c, genericPoint X ∈ B.U c := Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  refine ⟨fun u => fnOf _ h₀ (u.f c₀) / ρ c₀, fun u c hc => ?_⟩
  have e : fnOf _ hc (u.f c) = fnOf _ (memInf hc h₀) (B.g c c₀ : Γ(X, B.U c ⊓ B.U c₀)) * fnOf _ h₀ (u.f c₀) := by
    rw [← fnOf_resG inf_le_left (memInf hc h₀), ← fnOf_resG inf_le_right (memInf hc h₀), ← map_mul]
    exact congrArg _ (u.compat c c₀)
  rw [e, hρ c c₀ (memInf hc h₀)]
  have := (ρ c₀).ne_zero
  field_simp

theorem exists_sec {X : Scheme.{0}} [IsIntegral X] {B : LB X} {ρ : B.ι → X.functionFieldˣ}
    (hρ : IsRatSec B ρ) {f : X.functionField} (hf : ∀ c, ∀ x ∈ B.U c, RegAt x (f * ρ c)) :
    ∃ u : B.Sec, ∀ c (hc : genericPoint X ∈ B.U c), fnOf _ hc (u.f c) = f * ρ c := by
  have h : ∀ c, ∃ a : Γ(X, B.U c), ∀ hc, fnOf _ hc a = f * ρ c := fun c => by
    by_cases hc : genericPoint X ∈ B.U c
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hc (hf c)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (hc h).elim⟩
  choose a ha using h
  refine ⟨⟨a, fun i j => Cartier.fn_ext fun h => ?_⟩, ha⟩
  rw [map_mul]
  refine (fnOf_resG _ h _).trans (Eq.trans ?_ (congrArg (_ * ·) (fnOf_resG _ h _).symm))
  rw [ha, ha, hρ i j h]
  ring

theorem rep_dict : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∃ e : M.B.Sec → X.functionField, Function.Injective e ∧ Set.range e = (P.H a b : Set X.functionField) ∧ (∀ u (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y (e u) ^ 2 = (M.φ σ).nsq (secVal p σ u) y) ∧ ∀ u (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → (x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u ↔ UnitAt x (P.loc a b (e u) i j)) := by
  intro k _ X _ p P a b M ⟨ρ, hρ, hu, hn⟩
  obtain ⟨e, he⟩ := exists_quot M.isLB hρ
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  have hl (f : X.functionField) c i j :
      P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    simp only [Pair.loc]
    field_simp
  have hl' (f : X.functionField) c i j :
      P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹ := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    have := (ρ c).ne_zero
    simp only [Pair.loc]
    field_simp
  have hmem u : e u ∈ P.H a b := fun x i j hi hj => by
    obtain ⟨c, hc⟩ := hcov M.isLB x
    rw [hl' _ c, he u c (gen_mem hc)]
    exact (regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt
  refine ⟨e, fun u v huv => ?_, ?_, fun u σ y => ?_, fun u x i j hi hj => ?_⟩
  · refine ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext fun c => Cartier.fn_ext fun hc => ?_
    rw [← he, ← he, huv]
  · refine Set.Subset.antisymm (Set.range_subset_iff.2 hmem) fun f hf => ?_
    obtain ⟨u, hu'⟩ := exists_sec hρ (f := f) fun c x hc => by
      obtain ⟨i, hi⟩ := hcov P.L.isLB x
      obtain ⟨j, hj⟩ := hcov P.A.isLB x
      rw [← hl f c i j]
      exact (hf x i j hi hj).mul (hu x c i j hc hi hj).regAt
    obtain ⟨c, hc⟩ := hcov M.isLB (genericPoint X)
    exact ⟨u, mul_right_cancel₀ (ρ c).ne_zero ((he u c hc).trans (hu' c hc))⟩
  · have hi := mem_pick (P.L.φ σ).isLB y
    have hj := mem_pick (P.A.φ σ).isLB y
    have hc := mem_pick (M.φ σ).isLB y
    have hU := hu _ _ _ _ (mem_ptsIn.1 hc) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have h1 := hn σ y _ _ _ hc hi hj
    have h2 := ratVal_mul (y := y) (hmem u _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)) hU.regAt
    rw [hl, he u _ (gen_mem (mem_ptsIn.1 hc)), ratVal_fnOf hc] at h2
    have h3 := norm_pos_iff.2 (ratVal_ne_zero hU)
    rw [Pair.nu, Weight.nsq, secVal_apply, h2, ← h1, Real.exp_sub, Real.exp_log h3, norm_mul, Real.exp_neg]
    have h4 : Real.exp ((M.φ σ).φ (pick (M.φ σ).isLB y) y) =
        Real.exp ((M.φ σ).φ (pick (M.φ σ).isLB y) y / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h4]
    field_simp
  · obtain ⟨c, hc⟩ := hcov M.isLB x
    have hU := hu x c i j hc hi hj
    rw [mem_nonzeroLocus_iff u c hc, ← unitAt_fnOf_iff hc (gen_mem hc), ← he]
    exact ⟨fun h => hl' (e u) c i j ▸ h.mul hU.inv, fun h => hl (e u) c i j ▸ h.mul hU⟩

end GlobalTheory.VolBr.RepDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

namespace Pair

theorem unitAt_div_of_isRatSec (M : HermLB p) {ρ : M.B.ι → X.functionFieldˣ} (hρ : IsRatSec M.B ρ)
    {x : X} {c i : M.B.ι} (hc : x ∈ M.B.U c) (hi : x ∈ M.B.U i) :
    UnitAt x ((ρ c : X.functionField) / (ρ i : X.functionField)) := by
  have hx : x ∈ M.B.U c ⊓ M.B.U i := ⟨hc, hi⟩
  rw [hρ c i (gen_mem hx), mul_div_cancel_right₀ _ (ρ i).ne_zero]
  exact unitAt_fnOf hx _ _

theorem log_norm_div_of_isRatSec (M : HermLB p) {ρ : M.B.ι → X.functionFieldˣ} (hρ : IsRatSec M.B ρ)
    (σ : k →+* ℂ) {y : CxPts p σ} {c i : M.B.ι} (hc : y ∈ ptsIn p σ (M.B.U c))
    (hi : y ∈ ptsIn p σ (M.B.U i)) :
    Real.log ‖ratVal ((ρ c : X.functionField) / (ρ i : X.functionField)) y‖ - (M.φ σ).φ c y / 2 = -((M.φ σ).φ i y) / 2 := by
  have hy := mem_ptsIn_inf.2 ⟨hc, hi⟩
  rw [hρ c i (gen_mem (mem_ptsIn.1 hy)), mul_div_cancel_right₀ _ (ρ i).ne_zero, ratVal_fnOf hy,
    (M.φ σ).trans c i y hc hi, Real.log_pow]
  simp only [GlobalTheory.CxPts.gv]
  push_cast
  ring

end Pair

theorem Pair.rep_base (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (P : Pair p) : P.Rep 1 0 P.L ∧ P.Rep 0 1 P.A ∧ P.Rep 0 0 (HermLB.triv p) := by
  refine ⟨⟨P.r, P.hr, fun x c i j hc hi _ => ?_, fun σ y c i j hc hi _ => ?_⟩,
    ⟨P.r', P.hr', fun x c i j hc _ hj => ?_, fun σ y c i j hc _ hj => ?_⟩,
    ⟨fun _ => 1, presents_zero.isRatSec, fun x c i j _ _ _ => ?_, fun σ y c i j _ _ _ => ?_⟩⟩
  · have e : P.loc 1 0 1 i j = P.r i := by simp [Pair.loc]
    rw [e]
    exact Pair.unitAt_div_of_isRatSec P.L P.hr hc hi
  · have e : P.loc 1 0 1 i j = P.r i := by simp [Pair.loc]
    rw [e, Pair.log_norm_div_of_isRatSec P.L P.hr σ hc hi]
    push_cast
    ring
  · have e : P.loc 0 1 1 i j = P.r' j := by simp [Pair.loc]
    rw [e]
    exact Pair.unitAt_div_of_isRatSec P.A P.hr' hc hj
  · have e : P.loc 0 1 1 i j = P.r' j := by simp [Pair.loc]
    rw [e, Pair.log_norm_div_of_isRatSec P.A P.hr' σ hc hj]
    push_cast
    ring
  · have e : P.loc 0 0 1 i j = 1 := by simp [Pair.loc]
    rw [e, Units.val_one, div_one]
    exact unitAt_one x
  · have e : P.loc 0 0 1 i j = 1 := by simp [Pair.loc]
    have hv := ratVal_fnOf (y := y) mem_ptsIn_top trivial (1 : Γ(X, ⊤))
    rw [map_one, ev_one mem_ptsIn_top] at hv
    rw [e, Units.val_one, div_one, hv]
    simp [HermLB.triv, Weight.ofFun]

end GlobalTheory.VolBr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.VolBr.Pair

theorem isRatSec_dual_of_inv {X : Scheme.{0}} [IsIntegral X] {L : LB X} {r : L.ι → X.functionFieldˣ}
    (hr : IsRatSec L r) : IsRatSec (CechPic.dual L) fun i => (r i)⁻¹ := fun i j hij => by
  have e : fnOf _ hij ((CechPic.dual L).g i j : Γ(X, L.U i ⊓ L.U j)ˣ).val =
      (fnOf _ hij (L.g i j : Γ(X, L.U i ⊓ L.U j)))⁻¹ := map_units_inv _ _
  rw [e, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hr i j hij, mul_inv]
  rfl

theorem dual_quot_eq {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b : ℤ) (u : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    u⁻¹ / P.loc (-a) (-b) 1 i j = (u / P.loc a b 1 i j)⁻¹ := by
  simp only [loc, one_mul, zpow_neg, div_eq_mul_inv, mul_inv, inv_inv]

theorem ratVal_inv_unit {k : Type} [CommRing k] {σ : k →+* ℂ} {Z : Scheme.{0}} [IsIntegral Z]
    {q : Z ⟶ Sp k} {y : CxPts q σ} {f : Z.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have e := ratVal_mul (y := y) hf.regAt hf.inv.regAt
  have e1 := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
  rw [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e1
  rw [mul_inv_cancel₀ hf.ne_zero, e1] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem rep_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → P.Rep (-a) (-b) M.dual := by
  intro k _ X _ p P a b M ⟨ρ, hρ, hu, hn⟩
  refine ⟨fun c => (ρ c)⁻¹, isRatSec_dual_of_inv hρ, ?_, ?_⟩
  · intro x c i j hc hi hj
    rw [Units.val_inv_eq_inv_val, dual_quot_eq]
    exact (hu x c i j hc hi hj).inv
  · intro σ y c i j hc hi hj
    have hU := hu _ c i j (mem_ptsIn.1 hc) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have e := hn σ y c i j hc hi hj
    rw [Units.val_inv_eq_inv_val, dual_quot_eq, ratVal_inv_unit hU, norm_inv, Real.log_inv]
    change _ - (-(M.φ σ).φ c y) / 2 = _
    push_cast
    linarith

end GlobalTheory.VolBr.Pair
end
end

