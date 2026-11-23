module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingAdmissibleFacts
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalBundleOpenRestrict
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace CanonLB

open TopForm LB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {R : Type} [CommRing R] {X Y : Scheme.{0}} {f : X ⟶ Sp R} (e : Y ⟶ X) [IsOpenImmersion e]
  {d : ℕ} [SmoothOfRelativeDimension d f]

theorem comp_spMap_id (f : X ⟶ Sp R) : e ≫ f = (e ≫ f) ≫ spMap (RingHom.id R) := by
  simp [spMap]

theorem isFrame_pullForm_openImm {U : X.Opens} {ω : FormsOn f d U} (hω : IsFrame ω)
    {W : Y.Opens} (hW : IsAffineOpen W) (h : W ≤ e ⁻¹ᵁ U) :
    IsFrame (pullForm (comp_spMap_id e f) h ω) := by
  have hle : e ''ᵁ W ≤ U := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h hy
  have h' : W ≤ e ⁻¹ᵁ (e ''ᵁ W) := (e.preimage_image_eq W).ge
  have hω' : IsFrame (resForm hle ω) := hω.res (hW.image_of_isOpenImmersion e) hle
  have key : pullForm (comp_spMap_id e f) h ω = pullForm (comp_spMap_id e f) h' (resForm hle ω) := by
    rw [pullForm_resForm]
  rw [key]
  have hiso : IsIso (e.appLE (e ''ᵁ W) W h') := by
    have : e.appLE (e ''ᵁ W) W h' = (e.appIso W).hom := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]
      rfl
    rw [this]
    infer_instance
  have sq := appLE_comp_algX (comp_spMap_id e f) h'
  haveI : IsIso (CommRingCat.ofHom (e.appLE (e ''ᵁ W) W h').hom) := by
    simpa using hiso
  haveI : IsIso (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id]
    infer_instance
  have H : IsPushout (CommRingCat.ofHom (algX f (e ''ᵁ W))) (CommRingCat.ofHom (RingHom.id R))
      (CommRingCat.ofHom (e.appLE (e ''ᵁ W) W h').hom) (CommRingCat.ofHom (algX (e ≫ f) W)) := by
    refine IsPushout.of_vert_isIso ⟨?_⟩
    ext x
    exact RingHom.congr_fun sq x
  exact ⟨hW, hω'.gen.formMapSq (RingHom.id R) (e.appLE (e ''ᵁ W) W h').hom sq H⟩

abbrev OIdx (e : Y ⟶ X) (K : CanonLB f d) : Type :=
  Σ i : K.bundle.ι, {W : Y.Opens // IsAffineOpen W ∧ W ≤ e ⁻¹ᵁ K.bundle.U i}

def oBundle (e : Y ⟶ X) (K : CanonLB f d) : LB Y :=
  ZH.UFib.refinePull K.bundle e (fun a : OIdx e K => a.2.1) (fun a => a.1) (fun a => a.2.2.2)

theorem resG_oBundle_g (K : CanonLB f d) (a b : OIdx e K)
    {W : Y.Opens} (h : W ≤ (oBundle e K).U a ⊓ (oBundle e K).U b) :
    resG Y h ((oBundle e K).g a b : Γ(Y, (oBundle e K).U a ⊓ (oBundle e K).U b)) =
      (e.appLE (K.bundle.U a.1 ⊓ K.bundle.U b.1) W
        (h.trans (fun _ hy => ⟨a.2.2.2 hy.1, b.2.2.2 hy.2⟩))).hom
          ((K.bundle.g a.1 b.1 : Γ(X, K.bundle.U a.1 ⊓ K.bundle.U b.1))) := by
  simp only [oBundle, ZH.UFib.refinePull, res, pullU, Units.coe_map, MonoidHom.coe_coe]
  erw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  simp only [Scheme.Hom.appLE, Category.assoc, resG]
  rw [← Functor.map_comp]
  rfl

theorem iSup_oIdx (K : CanonLB f d) : ⨆ a : OIdx e K, a.2.1 = ⊤ :=
  eq_top_iff.2 fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart K.isLB (e y)
    obtain ⟨W, hW, hy, hsub⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := e ⁻¹ᵁ K.bundle.U i) hi
    exact Opens.mem_iSup.2 ⟨⟨i, W, hW, fun z hz => hsub hz⟩, hy⟩

def oChartPull (K : CanonLB f d) : ChartPull (oBundle e K) K.bundle e where
  idx a := a.1
  le a := a.2.2.2
  g y a b h h' := ZH.UFib.gm_refinePull K.bundle e (fun a : OIdx e K => a.2.1) (fun a => a.1)
    (fun a => a.2.2.2) y a b h h'

variable [SmoothOfRelativeDimension d (e ≫ f)]

theorem resForm_pullForm_om (K : CanonLB f d) (a b : OIdx e K) {W : Y.Opens} (hW : IsAffineOpen W)
    (ha : W ≤ a.2.1) (hb : W ≤ b.2.1) (h : W ≤ e ⁻¹ᵁ (K.bundle.U a.1 ⊓ K.bundle.U b.1)) :
    resForm hb (pullForm (comp_spMap_id e f) b.2.2.2 (K.om b.1)) =
      (e.appLE (K.bundle.U a.1 ⊓ K.bundle.U b.1) W h).hom
          ((K.bundle.g a.1 b.1 : Γ(X, K.bundle.U a.1 ⊓ K.bundle.U b.1))) •
        resForm ha (pullForm (comp_spMap_id e f) a.2.2.2 (K.om a.1)) := by
  have hfa := isFrame_pullForm_openImm e (K.isFrame a.1) a.2.2.1 a.2.2.2
  have h₁ := (K.isFrame a.1).coeff_pullForm (comp_spMap_id e f) a.2.2.2 hfa inf_le_left ha h
    (resForm inf_le_right (K.om b.1))
  rw [pullForm_resForm] at h₁
  rw [g_eq_ratio, resForm_pullForm]
  exact (hfa.coeff_smul_resForm hW ha _).symm.trans (congrArg (· • _) h₁)

def openImm (K : CanonLB f d) : CanonLB (e ≫ f) d where
  bundle := oBundle e K
  isLB := ZH.UFib.refinePull_isLB K.bundle K.isLB e _ _ _ (iSup_oIdx e K)
  affine a := a.2.2.1
  om a := pullForm (comp_spMap_id e f) a.2.2.2 (K.om a.1)
  gen a := (isFrame_pullForm_openImm e (K.isFrame a.1) a.2.2.1 a.2.2.2).gen
  trans a b W hW ha hb := by
    have h : W ≤ e ⁻¹ᵁ (K.bundle.U a.1 ⊓ K.bundle.U b.1) :=
      le_inf (ha.trans a.2.2.2) (hb.trans b.2.2.2)
    exact (resForm_pullForm_om e K a b hW ha hb h).trans
      (congrArg (· • _) (resG_oBundle_g e K a b (le_inf ha hb)).symm)

end CanonLB

theorem cls_canonLB_openImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R)
    (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) [SmoothOfRelativeDimension d f]
    [SmoothOfRelativeDimension d (e ≫ f)] (K : CanonLB f d) (K' : CanonLB (e ≫ f) d),
    cls K'.bundle K'.isLB = CechPic.pull e (cls K.bundle K.isLB) := by
  intro R _ X Y f e _ d _ _ K K'
  have hp : (K.bundle.pull e).IsLB := Semi.LB.isLB_linComb K.isLB _ _
  calc cls K'.bundle K'.isLB = cls (K.openImm e).bundle (K.openImm e).isLB :=
        (cls_eq_iff _ _).2 (K'.lbIso (K.openImm e))
    _ = cls (K.bundle.pull e) hp :=
        (cls_eq_iff _ _).2 (LBIso.chartPull (K.oChartPull e)
          (Geo.Tor.chartPullPull K.bundle e e rfl) (K.lbIso K))
    _ = CechPic.pull e (cls K.bundle K.isLB) := cls_pull K.isLB e hp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliCoeffDualWeylEqCoeffProd
section
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

noncomputable section

namespace GlobalTheory.CapelliCoeffs

open Polynomial

def entry (O : Type) [CommRing O] (N : ℕ) (α : Equiv.Perm (Fin N)) (k : Fin N) :
    Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  C (FreeAlgebra.ι O (α k, k)) + if α k = k then X - C (((k : ℕ) : FreeAlgebra O (Fin N × Fin N))) else 0

def capPoly (O : Type) [CommRing O] (N : ℕ) : Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  ∑ α : Equiv.Perm (Fin N), (((Equiv.Perm.sign α : ℤˣ) : ℤ) : Polynomial (FreeAlgebra O (Fin N × Fin N))) *
    (List.ofFn (entry O N α)).prod

theorem ofFn_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] (ψ : M →+ M') : ∀ {m : ℕ} (g : Fin m → Module.End R M)
    (g' : Fin m → Module.End S M'), (∀ k x, ψ (g k x) = g' k (ψ x)) →
    ∀ x, ψ ((List.ofFn g).prod x) = (List.ofFn g').prod (ψ x)
  | 0, g, g', _, x => by simp
  | m + 1, g, g', h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h 0, ofFn_intertwine ψ (fun k => g k.succ) (fun k => g' k.succ) (fun k => h k.succ)]

theorem capDet_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] {n : ℕ} (ψ : M →+ M') (E : Fin n → Fin n → Module.End R M)
    (E' : Fin n → Fin n → Module.End S M') (h : ∀ i j x, ψ (E i j x) = E' i j (ψ x)) (u : ℤ) (x : M) :
    ψ (Formalism.BranchingDeterminantCap.capDet E u x) = Formalism.BranchingDeterminantCap.capDet E' u (ψ x) := by
  unfold Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  refine ofFn_intertwine ψ _ _ (fun k y => ?_) x
  simp only [Formalism.BranchingDeterminantCap.bmF, LinearMap.sub_apply, map_sub, h]
  split_ifs
  · simp [Module.End.intCast_apply, map_zsmul]
  · simp

theorem capDet_dualWeyl_domain (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ)
    (hν : Antitone ν) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν) (u : ℤ) :
    Formalism.BranchingDeterminantCap.capDet (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1) u f =
      ((∏ j : Fin N, (u + ((j : ℕ) : ℤ) - (ν j : ℤ)) : ℤ) : O) • f := by
  let K := FractionRing O
  let φ : O →+* K := algebraMap O K
  have hφ : Function.Injective φ := IsFractionRing.injective O K
  have hg := Formalism.GradedWeylDivisibility.dualWeylMap O K φ N N ν f hf
  have h1 := GlobalTheory.BrCompare.capDet_dualWeyl (K := K) hν u hg
  have e : (fun i j => GlobalTheory.Mem.Gelf.rowE K N N i j) = fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1 := by
    funext a b
    exact LinearMap.ext fun P => (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv K N N a b P).1
  rw [e] at h1
  have h2 := capDet_intertwine (MvPolynomial.map φ).toAddMonoidHom (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1)
    (fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1) (fun i j x => (Formalism.GradedWeylDivisibility.lclosedeq_rowDiv_map φ i j 1 x).symm) u f
  apply MvPolynomial.map_injective φ hφ
  have h3 := h2.trans h1
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h3
  rw [h3, Int.cast_smul_eq_zsmul K, Int.cast_smul_eq_zsmul O, map_zsmul]

theorem eval_capPoly (O : Type) [CommRing O] (N : ℕ) {M : Type} [AddCommGroup M] [Module O M]
    (Φ : FreeAlgebra O (Fin N × Fin N) →ₐ[O] Module.End O M) (v : ℤ) (L : ℕ)
    (hL : (capPoly O N).natDegree < L) :
    ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) =
      ((-1 : ℤ) ^ N) • Formalism.BranchingDeterminantCap.capDet (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) := by
  have hc : ∀ a : Module.End O M, Commute ((RingHom.id _) a) (v : Module.End O M) :=
    fun a => (Int.cast_commute v a).symm
  let ev := Polynomial.eval₂RingHom' (RingHom.id (Module.End O M)) (v : Module.End O M) hc
  let Ψ := Polynomial.mapRingHom (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
  have key : ev (Ψ (capPoly O N)) = ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) := by
    show eval₂ (RingHom.id _) (v : Module.End O M) (map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
      (capPoly O N)) = _
    rw [eval₂_eq_sum_range' _ (lt_of_le_of_lt natDegree_map_le hL)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, RingHom.id_apply, ← Int.cast_pow, zsmul_eq_mul']
    rfl
  rw [← key]
  unfold capPoly Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hev : ∀ p, ev p = p.eval₂ (RingHom.id _) (v : Module.End O M) := fun _ => rfl
  have hΨ : ∀ p, Ψ p = p.map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M) := fun _ => rfl
  have e : (List.ofFn fun k => ev (Ψ (entry O N α k))) =
      (List.ofFn fun k => Formalism.BranchingDeterminantCap.bmF (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) k (α k) (id k)).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
    funext k
    rw [hev, hΨ]
    simp only [Function.comp_apply, entry, Formalism.BranchingDeterminantCap.bmF, id]
    split_ifs
    · simp only [Polynomial.map_add (f := _), Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval₂_add,
        Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.id_apply, map_natCast, RingHom.coe_coe, Polynomial.map_natCast,
        Polynomial.eval₂_natCast]
      push_cast
      abel
    · simp
  rw [show (⇑ev ∘ ⇑Ψ ∘ entry O N α) = fun k => ev (Ψ (entry O N α k)) from rfl, e, List.prod_map_neg, List.length_ofFn, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  exact (Int.cast_commute _ _).left_comm _

theorem coeff_eq_of_int (P : Type) [CommRing P] [IsDomain P] [CharZero P] (L : ℕ) (a b : ℕ → P)
    (h : ∀ v : ℤ, ∑ i ∈ Finset.range L, (v : P) ^ i * a i = ∑ i ∈ Finset.range L, (v : P) ^ i * b i) :
    ∀ i < L, a i = b i := by
  intro i hi
  let Q : Polynomial P := ∑ j ∈ Finset.range L, monomial j (a j - b j)
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Int.cast_injective (α := P)))
    rintro _ ⟨v, rfl⟩
    have hv := h v
    simp only [Set.mem_setOf_eq, IsRoot, Q, eval_finsetSum, eval_monomial]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hv
    rw [← hv]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := congrArg (fun q : Polynomial P => q.coeff i) hQ
  simp only [Q, finsetSum_coeff, coeff_monomial, coeff_zero] at this
  simp only [Finsupp.single_apply] at this
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg hj) (fun h' => absurd (Finset.mem_range.2 hi) h'), if_pos rfl] at this
  exact sub_eq_zero.1 this

end GlobalTheory.CapelliCoeffs

namespace GlobalTheory.CapelliCoeffs

open Polynomial

theorem capelli_coeff_dualWeyl : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ),
    ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν →
      ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ,
        evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  intro O _ _ _ N
  refine ⟨fun k => (capPoly O N).coeff k, fun ν hν f hf k => ?_⟩
  set p : Polynomial ℤ := ∏ a : Fin N, (X + C (((ν a : ℤ) - (a : ℕ) : ℤ))) with hpdef
  set L := (capPoly O N).natDegree + N + 1 with hLdef
  have hp : p.natDegree ≤ N := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => (natDegree_X_add_C (((ν a : ℤ) - (a : ℕ) : ℤ))).le).trans ?_
    simp
  have hE : (fun a b => evalPol O N (FreeAlgebra.ι O (a, b))) = fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1 := by
    funext a b
    simp [evalPol]
  by_cases hk : k < L
  · refine coeff_eq_of_int (MvPolynomial (Fin N × Fin N) O) L
      (fun i => evalPol O N ((capPoly O N).coeff i) f) (fun i => ((p.coeff i : ℤ) : O) • f) (fun v => ?_) k hk
    have hA := eval_capPoly O N (evalPol O N) v L (by omega)
    rw [hE] at hA
    have hB := capDet_dualWeyl_domain O N ν hν f hf (-v)
    have e1 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * evalPol O N ((capPoly O N).coeff i) f =
        (∑ i ∈ Finset.range L, (v ^ i) • evalPol O N ((capPoly O N).coeff i)) f := by
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, ← Int.cast_pow, ← zsmul_eq_mul]
    have e2 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * (((p.coeff i : ℤ) : O) • f) =
        (p.eval v) • f := by
      rw [eval_eq_sum_range' (n := L) (by omega), Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Int.cast_pow, ← zsmul_eq_mul, Int.cast_smul_eq_zsmul, smul_smul, mul_comm]
    have e3 : p.eval v = (-1 : ℤ) ^ N * ∏ j : Fin N, (-v + ((j : ℕ) : ℤ) - (ν j : ℤ)) := by
      rw [hpdef, eval_prod]
      have : ((-1 : ℤ) ^ N) = ∏ _j : Fin N, (-1 : ℤ) := by simp
      rw [this, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [eval_add, eval_X, eval_C]
      ring
    rw [e1, e2, hA, LinearMap.smul_apply, hB, e3, Int.cast_smul_eq_zsmul, smul_smul]
  · have h1 : (capPoly O N).coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    show evalPol O N ((capPoly O N).coeff k) f = _
    rw [h1, h2, map_zero]
    simp

end GlobalTheory.CapelliCoeffs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfHermitianMultiplicationModel
section
noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem charpoly_mulLeft_eq_of_gen {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (Q : F[X]) (hQ : Q.Monic) (hadj : Algebra.adjoin F {u} = ⊤) (hr : aeval u Q = 0)
    (hd : Module.finrank F A = Q.natDegree) : (LinearMap.mulLeft F u).charpoly = Q := by
  set P := (LinearMap.mulLeft F u).charpoly with hPdef
  have hP : P.Monic := LinearMap.charpoly_monic _
  have hPd : P.natDegree = Q.natDegree := by rw [hPdef, LinearMap.charpoly_natDegree, hd]
  by_cases hQ1 : Q = 1
  · subst hQ1
    rw [natDegree_one] at hPd
    exact Polynomial.eq_one_of_monic_natDegree_zero hP hPd
  set d := Q.natDegree with hddef
  let v : Fin d → A := fun i => u ^ (i : ℕ)
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro a _
    have ha : a ∈ Algebra.adjoin F {u} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨p, rfl⟩ := ha
    show aeval u p ∈ _
    rw [← Polynomial.aeval_modByMonic_eq_self_of_root hr,
      Polynomial.aeval_eq_sum_range' (Polynomial.natDegree_modByMonic_lt p hQ hQ1)]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩)
  have hli : LinearIndependent F v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hsp (by simp [hd, hddef])
  have hPu : aeval u P = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (LinearMap.mulLeft F u)
    have h2 : (Algebra.lmul F A) u = LinearMap.mulLeft F u := by ext; simp
    rw [← hPdef, ← h2, Polynomial.aeval_algHom_apply] at h1
    have h3 := congrArg (fun f : Module.End F A => f 1) h1
    simpa using h3
  by_contra hne
  have hR : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (P - Q).degree < d := by
    have := Polynomial.degree_sub_lt (p := P) (q := Q) (by rw [Polynomial.degree_eq_natDegree hP.ne_zero,
      Polynomial.degree_eq_natDegree hQ.ne_zero, hPd]) hP.ne_zero (by rw [hP.leadingCoeff, hQ.leadingCoeff])
    rwa [Polynomial.degree_eq_natDegree hP.ne_zero, hPd] at this
  have hRd : (P - Q).natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt hR).2 hdeg
  have hz : aeval u (P - Q) = 0 := by simp [hPu, hr]
  rw [Polynomial.aeval_eq_sum_range' hRd, Finset.sum_range (fun i => (P - Q).coeff i • u ^ i)] at hz
  have hc := (Fintype.linearIndependent_iff.1 hli) (fun i => (P - Q).coeff i) hz ⟨_, hRd⟩
  exact hR (Polynomial.leadingCoeff_eq_zero.1 hc)

theorem charpoly_of_semilinear {F L A : Type} [Field F] [Field L] [CommRing A] [Algebra F A] [Module.Finite F A]
    (e : F ≃+* L) {n : ℕ} (u : A) (g : Matrix (Fin n) (Fin n) L) (ψ : A ≃+ (Fin n → L))
    (hψ : ∀ (c : F) (y : A), ψ (c • y) = e c • ψ y) (hu : ∀ y, ψ (u * y) = g *ᵥ ψ y) :
    g.charpoly = (LinearMap.mulLeft F u).charpoly.map (e : F →+* L) := by
  let b := Module.finBasis F A
  set d := Module.finrank F A
  let v : Fin d → (Fin n → L) := fun i => ψ (b i)
  have hsum : ∀ c : Fin d → L, ∑ i, c i • v i = ψ (∑ i, e.symm (c i) • b i) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ, e.apply_symm_apply]
  have hli : LinearIndependent L v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [hsum, map_eq_zero_iff ψ ψ.injective] at hc
    have := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ hc i
    simpa using this
  have hsp : ⊤ ≤ Submodule.span L (Set.range v) := by
    intro x _
    obtain ⟨a, rfl⟩ := ψ.surjective x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin d) L (Fin n → L) := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = v i := fun i => Module.Basis.mk_apply hli hsp i
  let M := LinearMap.toMatrix b b (LinearMap.mulLeft F u)
  have key : LinearMap.toMatrix b' b' (Matrix.toLin' g) = M.map (e : F →+* L) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, hb', Matrix.toLin'_apply]
    have h1 : g *ᵥ v j = ∑ k, e (b.repr (u * b j) k) • b' k := by
      show g *ᵥ ψ (b j) = _
      rw [← hu]
      conv_lhs => rw [← b.sum_repr (u * b j)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hψ, hb']
    rw [h1, b'.repr_sum_self]
    simp [M, LinearMap.toMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul]
  calc g.charpoly = (Matrix.toLin' g).charpoly := by
        rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' g) (Pi.basisFun L (Fin n)),
          LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    _ = (M.map (e : F →+* L)).charpoly := by rw [← key, LinearMap.charpoly_toMatrix]
    _ = _ := by rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

theorem charpoly_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) (γ : GLw n w), Q.Monic → Fits w e B Q u → IsModel w e B u x γ → γ.val.charpoly = Q := by
  intro E _ _ _ w K e n Q B u x γ hQ hfit hmod
  obtain ⟨hadj, hr, hd, -⟩ := hfit
  obtain ⟨ψ, hψ, hu, -⟩ := hmod
  rw [charpoly_of_semilinear e u γ.val ψ hψ hu,
    charpoly_mulLeft_eq_of_gen u (Q.map e.symm.toRingHom) (hQ.map _) hadj hr (by rw [hd, natDegree_map]),
    Polynomial.map_map]
  ext i
  simp [Polynomial.coeff_map]

end GlobalTheory.KapLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMulLeftGeneratorEqMapSymm
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory

theorem charpoly_mulLeft_eq_of_adjoin_eq_top {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (u : A) (P : F[X]) (hP : P.Monic) (hadj : Algebra.adjoin F {u} = ⊤)
    (hu : aeval u P = 0) (hdim : Module.finrank F A = P.natDegree) :
    (LinearMap.mulLeft F u).charpoly = P := by
  have hint : IsIntegral F u := ⟨P, hP, hu⟩
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hgen : pb.gen = u := PowerBasis.ofAdjoinEqTop_gen hint hadj
  have hmin : minpoly F u = P := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hP (minpoly.dvd F u hu) ?_).symm
    rw [← hdim, pb.finrank, PowerBasis.ofAdjoinEqTop_dim]
  have h1 := charpoly_leftMulMatrix pb
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, hgen, hmin] at h1
  exact h1

theorem charpoly_mulLeft_eq_map_symm : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (R : Type) [Field R] (e : K.E ≃+* R) (u : B.A) (Q : R[X]), Q.Monic → Algebra.adjoin K.E {u} = ⊤ → aeval u (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom := by
  intro K B R _ e u Q hQ hadj hu hdim
  exact charpoly_mulLeft_eq_of_adjoin_eq_top u _ (hQ.map _) hadj hu (by rw [hdim, hQ.natDegree_map])

end GlobalTheory
end

