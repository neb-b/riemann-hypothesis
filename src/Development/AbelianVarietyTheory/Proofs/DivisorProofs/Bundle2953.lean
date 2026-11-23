module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1FiniteGenerationAffine
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin
open GlobalTheory.CatCoh GlobalTheory.CechDR

theorem isCoc_sub {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens) {c c' : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCoc W c) (hc' : IsCoc W c') : IsCoc W (fun i i' => c i i' - c' i i') := by
  intro i i' i''
  simp only [map_sub]
  linear_combination hc i i' i'' - hc' i i' i''

theorem cechFG_of_finite (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) [CompactSpace Z]
    (hfin : Module.Finite R (HO1 s)) (J : Type) (W : J → Z.Opens)
    (hD : ∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) (hc : ⨆ i, W i = ⊤) :
    CechFG W R (fun i i' => (secMap s (W i ⊓ W i')).hom) := by
  classical
  have hW : ∀ i, IsAffineOpen (W i) := fun i => by simpa using hD {i} (Finset.singleton_nonempty i)
  have hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i') := fun i i' => by
    have h := hD {i, i'} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_singleton] at h
  have hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'') := fun i i' i'' => by
    have h := hD {i, i', i''} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_insert, Finset.iInf_singleton, ← inf_assoc] at h
  obtain ⟨S, hS⟩ : ∃ S : Finset J, ⨆ i ∈ S, W i = ⊤ := by
    have hcov : (Set.univ : Set Z) ⊆ ⋃ i, (W i : Set Z) := by
      intro x _
      have hx : x ∈ ⨆ i, W i := hc ▸ trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      exact Set.mem_iUnion.2 hx
    obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (W i : Set Z)) (fun i => (W i).isOpen) hcov
    refine ⟨S, eq_top_iff.2 fun x _ => ?_⟩
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨hi, hx⟩⟩
  have hsur : ∀ c, IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i i',
      c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
    intro c hcoc
    obtain ⟨f, h₀, hf⟩ := _root_.GlobalTheory.CechFin.cocycle_of_finite_affine_subcover R Z s J W hW hW2 hD S hS c hcoc
    obtain ⟨h, hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover Z J W (↑S) (fun i => by
        rw [show (⨆ a ∈ (↑S : Set J), W a) = ⨆ a ∈ S, W a from by simp, hS]; exact le_top)
      (fun i i' => c i i' - rho W s hW hW2 f.1 i i') (isCoc_sub W hcoc (rho_isCoc W s hW hW2 hW3 f)) h₀
      (fun a ha b hb => by rw [hf a ha b hb]; ring)
    exact ⟨f, h, fun i i' => by rw [← hh]; ring⟩
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := HO1 s)
  choose fk hfk using fun k => H1.mk_surjective (OAff s) (v k)
  refine ⟨n, fun k => rho W s hW hW2 (fk k).1, fun k => rho_isCoc W s hW hW2 hW3 (fk k), fun c hcoc => ?_⟩
  obtain ⟨f, h, hfh⟩ := hsur c hcoc
  have hmem : H1.mk (OAff s) f ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  have hcl : H1.mk (OAff s) f = H1.mk (OAff s) (∑ k, r k • fk k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hr]
    simp only [map_smul, hfk]
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hcl
  have e1 : f.1 = (∑ k, r k • (fk k).1) + d0 (OAff s) g := by
    rw [hg, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    abel
  refine ⟨r, fun i => h i + (-gv s g ⟨W i, hW i⟩), fun i i' => ?_⟩
  rw [hfh, e1, rho_add, rho_sum, rho_d0, map_add (f := _), map_add (f := _)]
  ring

end GlobalTheory.CechFin

open GlobalTheory.CechFin in
theorem GlobalTheory.CechFin.cech_h1_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1), ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i'), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (r : Fin N → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  intro E _ _ _ H X t hP hA U J W hWaff hcov hWU
  obtain ⟨hcomp, hD, htop⟩ := _root_.GlobalTheory.pullback_fromSpec_compact_affineCover E H X t hP U J W hWaff hcov
  have hfin := _root_.GlobalTheory.CechFinGen.finite_HO1_onAff E H X t hP U
  exact GlobalTheory.T.cech_finite_generation_of_affine_base_change t.G.left X t.G.hom U J W hWU
    (cechFG_of_finite Γ(X, U.1) (pullback t.G.hom U.2.fromSpec) (pullback.snd t.G.hom U.2.fromSpec) hfin J _ hD htop)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRingActionCompatibleExtended
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChart

theorem denseRange_jK (R : Type) [CommRing R] [IsDomain R] : DenseRange (jK R) := by
  let ξ : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  intro y
  have hs : jK R ξ ⤳ y := (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => by
    have h₁ : algebraMap R (FractionRing R) a ∈ IsLocalRing.maximalIdeal (FractionRing R) := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h₁
    obtain rfl : a = 0 := IsFractionRing.injective R (FractionRing R) (h₁.trans (map_zero _).symm)
    exact Ideal.zero_mem _
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (f := jK R) ξ)) (specializes_iff_mem_closure.1 hs)

theorem isDominant_of_isPullback_jK {R : Type} [CommRing R] [IsDomain R] {X X' : Scheme.{0}}
    (p : X ⟶ Sp R) [Smooth p] (p' : X' ⟶ Sp (FractionRing R)) (φ : X' ⟶ X) (h : IsPullback φ p' p (jK R)) :
    IsDominant φ := by
  have hd : IsDominant (pullback.fst p (jK R)) := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Pullback.range_fst]
    exact (denseRange_jK R).preimage p.isOpenMap
  have e : h.isoPullback.hom ≫ pullback.fst p (jK R) = φ := h.isoPullback_hom_fst
  rw [← e]
  infer_instance

theorem act_chart_compat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] (tC : SAB H (Sp R)) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp R ⟶ S)
    (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (act : OAct (𝓞 E) G)
    (tK : SAB H (Sp (FractionRing R))) (a : SABMap tK tC (jK R)) (ψ : tK.G.left ⟶ G.left),
    (∀ u, (tK.act.act u).left ≫ ψ = ψ ≫ (act.act u).left) → a.φ ≫ πC = ψ →
    ∀ u, (tC.act.act u).left ≫ πC = πC ≫ (act.act u).left := by
  intro E _ _ _ H R _ _ tC S G _ _ ξ πC hG hP act tK a ψ hψ hφ u
  haveI : IsSeparated G.hom := hG.separated
  haveI : Smooth tC.G.hom := tC.semi.smooth
  haveI : IsReduced tC.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced tC.G.hom
  haveI : IsDominant a.φ := isDominant_of_isPullback_jK tC.G.hom tK.G.hom a.φ a.cart.1
  have hw : πC ≫ G.hom = tC.G.hom ≫ ξ := hP.1.w
  refine ext_of_isDominant_of_isSeparated G.hom ?_ a.φ ?_
  · rw [Category.assoc, Category.assoc, hw, Over.w (act.act u), hw, ← Category.assoc, Over.w (tC.act.act u)]
  · have e : (tK.act.act u).left ≫ a.φ = a.φ ≫ (tC.act.act u).left := a.act u
    rw [← Category.assoc, ← e, Category.assoc, hφ, hψ, ← hφ, Category.assoc]

end GlobalTheory.UChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreRemIndep
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatRatio.Closed

open GlobalTheory.KS GlobalTheory.KS.GlueDer

theorem gs_stalk {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    gs r z U a = (r.stalkMap z).hom (gs (𝟙 Y) (r z) U a) := by
  rw [gs_eq r z U h, gs_eq (𝟙 Y) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h a).symm

theorem exists_sval_stalk {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    ∃ J', Good L (r z) J' ∧ ∀ s : LB.Sec (LB.LinComb L φ ε),
      sval s r z J = (r.stalkMap z).hom (sval s (𝟙 Y) (r z) J') := by
  obtain ⟨J', hJ', e⟩ := exists_good L hL (r z) φ (fun k => J (r ≫ φ k)) (fun a b e => by rw [e])
    (fun k => hJ (r ≫ φ k))
  refine ⟨J', hJ', fun s => ?_⟩
  rw [sval_of s (𝟙 Y) (r z) J' (fun k => J (r ≫ φ k)) (fun k => by rw [Category.id_comp]; exact e k)]
  exact gs_stalk r z _ (hJ.mem φ r) _

section Op

variable {R : Type} [CommRing R] {G : Over (Sp R)} {n : ℕ} {X : Scheme.{0}} {m : G.left ⟶ X} {L : LB X}
  {dd : Fin n → Fld G.left} {D : R → R} (h : Heat G m L dd D) (hdd : ∀ a, IsField ⊤ (dd a))
include hdd

theorem rsT_op (k : ℕ) (i : h.J) (O : G.left.Opens) (hO : O ≤ h.W i) (f : Γ(G.left, h.W i)) :
    rsT (op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) O =
      op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (rsT f O) := by
  have hd : ∀ g, resG G.left hO (h.d i (h.W i) g) = h.d i O (resG G.left hO g) :=
    fun g => ((h.lift i).1.2.2 (h.W i) O hO le_rfl g).symm
  have hdd' : ∀ a g, resG G.left hO (dd a (h.W i) g) = dd a O (resG G.left hO g) :=
    fun a g => ((hdd a).2.2 (h.W i) O hO le_top g).symm
  have hc : ∀ r, resG G.left hO (constFn G.hom (h.W i) r) = constFn G.hom O r :=
    fun r => res_const G.hom hO r
  have hp : ∀ q : Γ(G.left, h.W i), resG G.left hO (rsT q (h.W i)) = rsT q O := fun q => by
    rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
  rw [rsT_of_le hO, rsT_of_le hO]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [op, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]

theorem rem_eq (k : ℕ) (i : h.J) (O : G.left.Opens) (hO : O ≤ h.W i) {A : Type} [CommRing A] (π : Γ(G.left, O) →+* A)
    (hΘ : ∀ a b, π (constFn G.hom O (h.Θ a b)) = 0) (F T g : Γ(G.left, O)) (hT : IsUnit T)
    (e : op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (F * T) =
      F * op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O T + g * T) :
    π g - 2 * (k : A) * π (h.d i O F) = 2 * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O F) := by
  have e₁ := congrArg π e
  have hs : ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O (F * T)) =
      π F * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O T) + π T * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O F) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hdd a).2.1 O le_top, map_add (f := _), map_mul, map_mul]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [op, map_add (f := _), map_sub, map_mul, map_sum, hΘ, zero_mul, Finset.sum_const_zero, sub_zero, map_ofNat, map_pow,
    map_natCast] at e₁
  rw [hs, (h.lift i).1.2.1 O hO, map_add (f := _), map_mul, map_mul] at e₁
  refine (hT.map π).mul_left_cancel ?_
  linear_combination -e₁

end Op

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

theorem exists_term_germ (N : ℕ) (β : Q.X) (j : Q.P.L.ι) (V : Y.H.left.Opens) (hV : V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j)
    (y : Y.H.left) (hy : y ∈ V) : ∃ (J' : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι) (c : (Y.H.left.presheaf.stalk y)ˣ),
      Good Q.P.L (Y.q.left y) J' ∧ ∀ σ τ, IsTerm Y N β σ τ →
        gs (𝟙 _) y V (rsT (τ.f fun _ => j) V) = (Y.q.left.stalkMap y).hom (sval σ (𝟙 _) (Y.q.left y) J') * c.val := by
  obtain ⟨J, hJ, e⟩ := exists_good Q.P.L Q.P.isLB y (K := Unit) (fun _ => Y.q.left) (fun _ => j) (fun _ _ _ => rfl)
    (fun _ => hV hy)
  obtain ⟨J', hJ', e'⟩ := exists_sval_stalk Q.P.isLB (DegPre.famφB Q β) (DegPre.famε N) Y.q.left y hJ
  refine ⟨J', val ((Y.Φ Y.H (𝟙 _)).s β) (𝟙 _) y J, hJ', fun σ τ hτ => ?_⟩
  have h1 := hτ Y.H (𝟙 _) y J hJ
  rw [Category.id_comp, e'] at h1
  refine Eq.trans ?_ h1
  have hle : V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => j) := Glue.le_wchart _ hV
  refine Eq.trans ?_ (sval_of τ (𝟙 _) y J (fun _ => j) (fun _ => by rw [Category.id_comp]; exact e ())).symm
  exact (congrArg (gs (𝟙 _) y V) (rsT_of_le hle _)).trans (gs_res (𝟙 _) y hle hy _)

theorem rem_chart (hdd : ∀ a, IsField ⊤ (dd a)) (N : ℕ) (β : Q.X) (σ σ' σp σp' : Q.SecB N β) (U : Q.P.A.left.Opens)
    (f g : Γ(Q.P.A.left, U)) (hr : IsRatio Q σ σ' U f) (h₁ : TActs Y h N β σ σp) (h₂ : TActs Y h N β σ' σp')
    (hg : IsRem Q σ' σp σp' U f g) (i : h.J) (W : Q.P.A.left.Opens) (hWU : W ≤ U) (hW : Y.q.left ⁻¹ᵁ W ≤ h.W i)
    {A : Type} [CommRing A] (π : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W) →+* A)
    (hΘ : ∀ a b, π (constFn Y.H.hom _ (h.Θ a b)) = 0) :
    π ((Y.q.left.app W).hom (resG _ hWU g)) - 2 * (N : A) * π (h.d i _ ((Y.q.left.app W).hom (resG _ hWU f))) =
      2 * ∑ a, π (constFn Y.H.hom _ (h.u a)) * π (dd a _ ((Y.q.left.app W).hom (resG _ hWU f))) := by
  obtain ⟨τ, τp, t₁, t₂, a₁⟩ := h₁
  obtain ⟨τ', τp', t₃, t₄, a₂⟩ := h₂
  have hV := hW.trans (h.le i)
  have hWc : h.W i ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i) := Glue.le_wchart _ (h.le i)
  have hfn : ∀ y ∈ Y.q.left ⁻¹ᵁ W, ∀ x : Γ(Q.P.A.left, U),
      gs (𝟙 _) y (Y.q.left ⁻¹ᵁ W) ((Y.q.left.app W).hom (resG _ hWU x)) =
        (Y.q.left.stalkMap y).hom (gs (𝟙 _) (Y.q.left y) U x) := fun y hy x => by
    rw [gs_pull (𝟙 _) Y.q.left y W hy, Category.id_comp]
    exact (gs_res Y.q.left y hWU hy x).trans (gs_stalk _ y U (hWU hy) x)
  have act : ∀ {s s' : SecM Y.q.left Q.P.L N}, h.Acts N s s' → rsT (s'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) =
      op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) N _ (rsT (s.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W)) := fun {s s'} a => by
    have := congrArg (fun x => rsT x (Y.q.left ⁻¹ᵁ W)) (a i)
    simp only [rsT_op h hdd N i _ hW] at this
    exact (rsT_rsT hWc hW _).symm.trans (this.trans (congrArg _ (rsT_rsT hWc hW _)))
  have e₁ : rsT (τ.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) =
      (Y.q.left.app W).hom (resG _ hWU f) * rsT (τ'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) := fn_ext fun y hy => by
    obtain ⟨J', c, hJ', e⟩ := exists_term_germ Y N β (h.j i) _ hV y hy
    rw [gs_mul (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, hfn y hy, e σ τ t₁, e σ' τ' t₃, (hr _ (hWU hy) J' hJ').2, map_mul, _root_.mul_assoc]
  have e₂ : rsT (τp.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) =
      (Y.q.left.app W).hom (resG _ hWU f) * rsT (τp'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) +
      (Y.q.left.app W).hom (resG _ hWU g) * rsT (τ'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) := fn_ext fun y hy => by
    obtain ⟨J', c, hJ', e⟩ := exists_term_germ Y N β (h.j i) _ hV y hy
    rw [gs_add (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, gs_mul (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, gs_mul (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, hfn y hy, hfn y hy, e σp τp t₂, e σ' τ' t₃, e σp' τp' t₄,
      hg _ (hWU hy) J' hJ', map_add, map_mul, map_mul]
    ring
  have hu : IsUnit (rsT (τ'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W)) :=
    Y.H.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨J', c, hJ', e⟩ := exists_term_germ Y N β (h.j i) _ hV y hy
      exact (congrArg IsUnit ((gs_eq (𝟙 _) y _ hy _).symm.trans (e σ' τ' t₃))).mpr
        (((hr _ (hWU hy) J' hJ').1.map _).mul c.isUnit)
  refine rem_eq h hdd N i _ hW π hΘ _ _ _ hu ?_
  rw [← e₁, ← act a₁, ← act a₂, e₂]

theorem rem_indep (hdd : ∀ a, IsField ⊤ (dd a)) (hB : IsBasic Y h) {K : Type} [Field K] (φ : R →+* K)
    (hΘ : ∀ a b, φ (h.Θ a b) = 0) {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left)
    (hm : m ≫ Q.P.A.hom = p ≫ spMap φ) (dl : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(Z, m ⁻¹ᵁ W)) {D' : R → K}
    (hdl : LocDerK p Q.P.A.hom m D' ⊤ dl)
    (desc : ∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ Z), a ≫ Y.q.left = b ≫ m →
      ∀ (i : h.J) (W : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) =
        pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m ⁻¹ᵁ W)))
    (N₁ N₂ : ℕ) (β₁ β₂ : Q.X) (σ σ' σp σp' : Q.SecB N₁ β₁) (ρ ρ' ρp ρp' : Q.SecB N₂ β₂) (U : Q.P.A.left.Opens)
    (f g₁ g₂ : Γ(Q.P.A.left, U)) (r₁ : IsRatio Q σ σ' U f) (r₂ : IsRatio Q ρ ρ' U f)
    (h₁ : TActs Y h N₁ β₁ σ σp) (h₂ : TActs Y h N₁ β₁ σ' σp') (h₃ : TActs Y h N₂ β₂ ρ ρp) (h₄ : TActs Y h N₂ β₂ ρ' ρp')
    (e₁ : IsRem Q σ' σp σp' U f g₁) (e₂ : IsRem Q ρ' ρp ρp' U f g₂) :
    (m.app U).hom g₁ - 2 * (N₁ : Γ(Z, m ⁻¹ᵁ U)) * dl U f = (m.app U).hom g₂ - 2 * (N₂ : Γ(Z, m ⁻¹ᵁ U)) * dl U f := by
  have := Y.smooth_q
  have hs := (AbConst.surjective_q Y).1
  choose V hV using fun i => (hB i).1
  refine eq_of_rsT_eq (fun i => m ⁻¹ᵁ (U ⊓ V i)) (fun i => pre_mono m inf_le_left) (fun y hy => ?_) _ _ fun i => ?_
  · obtain ⟨x, hx⟩ := Y.q.left.surjective (m y)
    have hx' : x ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    rw [hV] at hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hx ▸ hi⟩
  obtain ⟨W, hWe⟩ : ∃ W, W = U ⊓ V i := ⟨_, rfl⟩
  have hWU : W ≤ U := hWe.le.trans inf_le_left
  have hW : Y.q.left ⁻¹ᵁ W ≤ h.W i := (pre_mono _ (hWe.le.trans inf_le_right)).trans (hV i).ge
  rw [← hWe]
  have red : ∀ (N : ℕ) (g : Γ(Q.P.A.left, U)), rsT ((m.app U).hom g - 2 * (N : Γ(Z, m ⁻¹ᵁ U)) * dl U f) (m ⁻¹ᵁ W) =
      (m.app W).hom (resG _ hWU g) - 2 * (N : Γ(Z, m ⁻¹ᵁ W)) * dl W (resG _ hWU f) := fun N g => by
    rw [hdl.res U W hWU le_top, rsT_of_le (pre_mono m hWU), rsT_of_le (pre_mono m hWU), map_sub, map_mul, map_mul,
      map_natCast, map_ofNat, res_app m hWU]
  rw [red, red]
  let a := pullback.fst Y.q.left m
  let b := pullback.snd Y.q.left m
  have w : a ≫ Y.q.left = b ≫ m := pullback.condition
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  let π := (a.appLE _ _ hle).hom
  have key : ∀ x, (b.app _).hom ((m.app W).hom x) = π ((Y.q.left.app W).hom x) := fun x => by
    have k : ∀ (c : pullback Y.q.left m ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W),
        (b.app _).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
      rintro _ rfl hc
      rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE b]
      rfl
    rw [k _ w hle]
    exact congrArg (fun ψ => ψ.hom x) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)
  have hc : ∀ r, π (constFn Y.H.hom _ r) = constFn (b ≫ p) _ (φ r) := fun r => by
    rw [← res_const (b ≫ p) hle, ← app_const φ Y.H.hom (b ≫ p) a (by
      rw [← Over.w Y.q, reassoc_of% w, hm, Category.assoc])]
    rfl
  have hΘ' : ∀ a b, π (constFn Y.H.hom _ (h.Θ a b)) = 0 := fun a b => by
    rw [hc, hΘ, constFn, map_zero, map_zero]
  have hd : ∀ x, (b.app _).hom (dl W x) = π (h.d i _ ((Y.q.left.app W).hom x)) := fun x => by
    have := desc _ a b w i W hW x
    rw [pbT, pbT, dite_eq_left le_rfl, dite_eq_left hle] at this
    rw [Scheme.Hom.app_eq_appLE b]
    exact this
  refine GlobalTheory.FunDescent.app_injective b _ ?_
  show (b.app _).hom _ = (b.app _).hom _
  simp only [map_sub, map_mul, map_natCast, map_ofNat, key, hd]
  exact (rem_chart Y h hdd N₁ β₁ σ σ' σp σp' U f g₁ r₁ h₁ h₂ e₁ i W hWU hW π hΘ').trans
    (rem_chart Y h hdd N₂ β₂ ρ ρ' ρp ρp' U f g₂ r₂ h₃ h₄ e₂ i W hWU hW π hΘ').symm

end Ray

theorem closed_fibre_rem_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (i : h.J) (W : P.D.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W))) → ∀ (N₁ N₂ : ℕ), 1 ≤ N₁ → 1 ≤ N₂ → ∀ (β₁ β₂ : P.D.toPre.X) (σ σ' σp σp' : P.D.toPre.SecB N₁ β₁) (ρ₂ ρ₂' ρp ρp' : P.D.toPre.SecB N₂ β₂) (U : P.D.toPre.P.A.left.Opens) (f g₁ g₂ : Γ(P.D.toPre.P.A.left, U)), GlobalTheory.HeatRatio.IsRatio P.D.toPre σ σ' U f → GlobalTheory.HeatRatio.IsRatio P.D.toPre ρ₂ ρ₂' U f → TActs Y h N₁ β₁ σ σp → TActs Y h N₁ β₁ σ' σp' → TActs Y h N₂ β₂ ρ₂ ρp → TActs Y h N₂ β₂ ρ₂' ρp' → GlobalTheory.HeatRatio.IsRem P.D.toPre σ' σp σp' U f g₁ → GlobalTheory.HeatRatio.IsRem P.D.toPre ρ₂' ρp ρp' U f g₂ → (m₀.app U).hom g₁ - 2 * (N₁ : Γ(A₀.left, m₀ ⁻¹ᵁ U)) * dl U f = (m₀.app U).hom g₂ - 2 * (N₂ : Γ(A₀.left, m₀ ⁻¹ᵁ U)) * dl U f := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _
  letI := H.starRing
  intro Y n' v' dd hdd D q _ h hB hΘ ρ hρ A₀ _ m₀ hm dl hdl desc N₁ N₂ _ _ β₁ β₂ σ σ' σp σp' ρ₂ ρ₂' ρp ρp' U f g₁ g₂
    r₁ r₂ h₁ h₂ h₃ h₄ e₁ e₂
  refine rem_indep Y h (fun a => (hdd a).1) hB ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) (fun a b => ?_) A₀.hom m₀
    hm.1.w dl hdl desc N₁ N₂ β₁ β₂ σ σ' σp σp' ρ₂ ρ₂' ρp ρp' U f g₁ g₂ r₁ r₂ h₁ h₂ h₃ h₄ e₁ e₂
  have h0 : MvPowerSeries.constantCoeff (h.Θ a b) = 0 := by
    by_contra hne
    exact hΘ a b (MvPowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne))
  show (ρ (h.Θ a b)).fst = 0
  simp [hρ, h0]

end GlobalTheory.HeatRatio.Closed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ChartNotAb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem subsingleton_of_closed_mem_abLocus {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {t : SAB H (Sp R)}
    (P : PELUnif (maximalIdeal R) t) (hc : (closedPoint R : Sp R) ∈ abLocus t.G) : Subsingleton P.D.toPre.X := by
  have hmax : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : maximalIdeal R ^ (0 + 1) ≤ (closedPoint R).asIdeal := by
    rw [zero_add, pow_one]; exact le_rfl
  obtain ⟨q, hq⟩ : closedPoint R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hq' : thick R (maximalIdeal R) 0 q ∈ abLocus t.G := by
    rw [← hq] at hc; exact hc
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF _ q hq' P.D.toPre.X g.i g.i_hom

end GlobalTheory.ChartNotAb


open GlobalTheory.ChartNotAb in
theorem GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → 1 ≤ C.m → closedPoint (ChartRing k m e) ∉ abLocus C.t.G := by
  intro E _ _ _ H Dw l Xo c φ k _ m e C hT hm hc
  obtain ⟨-, -, -, -, -, ⟨N, s, ε, τ₀, -, hε, -, -⟩, -⟩ := hT
  have hs := subsingleton_of_closed_mem_abLocus C.P hc
  let i : Fin C.m := ⟨0, hm⟩
  apply ε.ne_zero (Sum.inl i)
  apply Subtype.ext
  rw [Submodule.coe_zero, hε i]
  ext x y
  rw [Subsingleton.elim x 0]
  simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtensionIsoOfHodgeDeRham
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem deRhamVectorExtension_of_abelianHodgeDeRham :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DeRhamVectorExtension := by
  intro hHdR p _
  obtain ⟨e, hN, hF, hT, -⟩ := _root_.GlobalTheory.DeRhamExt.exists_canonical_family hHdR p
  exact ⟨e, hN, hF, hT⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalRestrictionRelAmpleLocusOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_restriction_relAmple_locus_open : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.DiagAmpleLocus.diag_relAmple_locus) | (exact GlobalTheory.DiagAmpleLocus.diag_relAmple_locus) | (intros; apply GlobalTheory.DiagAmpleLocus.diag_relAmple_locus  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelStaysDividingDeeperModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividingLabel_stays_dividing_deeper_model : (∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂) := by
  first | exact @GlobalTheory.Poinc.Sep.DeepDiv.div_lam | exact GlobalTheory.Poinc.Sep.DeepDiv.div_lam | (intros; apply GlobalTheory.Poinc.Sep.DeepDiv.div_lam <;> assumption)
end

