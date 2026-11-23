module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HolUnifSec

open GlobalTheory.CxPts Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {g : ℕ} (u : HolUnif A M g)

def pt (z : Fin g → ℂ) : CxPts A.hom (RingHom.id ℂ) :=
  ⟨(u.ex z).left, (Over.w (u.ex z)).trans (Spec.map_id _).symm⟩

theorem pt_surjective : Function.Surjective (pt u) := fun y => by
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk y.1 (y.2.trans (Spec.map_id _)))
  exact ⟨z, Subtype.ext (congrArg (·.left) hz)⟩

theorem sub_mem_of_pt_eq {z w : Fin g → ℂ} (h : pt u z = pt u w) : z - w ∈ u.Λ := by
  have h' : u.ex z = u.ex w := Over.OverMorphism.ext (congrArg Subtype.val h)
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, h'] at e
  exact (u.ker _).1 (mul_eq_right.1 e.symm)

theorem isOpen_pre (U : A.left.Opens) : IsOpen (pt u ⁻¹' ptsIn _ _ U) := (u.hol U 0).1

theorem differentiableOn_ev (U : A.left.Opens) (f : Γ(A.left, U)) :
    DifferentiableOn ℂ (ev _ _ U f ∘ pt u) (pt u ⁻¹' ptsIn _ _ U) := (u.hol U f).2

theorem continuous_pt : Continuous (pt u) :=
  CxPts.continuous_iff.2 fun U => ⟨isOpen_pre u U, fun f => (differentiableOn_ev u U f).continuousOn⟩

theorem eq_zero_of_fderiv_eq_zero (z₀ w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) z₀ w = 0) : w = 0 := by
  refine TorusTransfer.eq_zero_of_fderiv_eq_zero u w fun U f h => ?_
  let T : A ⟶ A := (toUnit A ≫ u.ex (-z₀)) * 𝟙 A
  have hT : ∀ z, (u.ex z).left ≫ T.left = (u.ex (-z₀ + z)).left := fun z => by
    rw [← Over.comp_left, u.ex_add]
    congr 1
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _),
      Category.id_comp]
  have h1 := hw (T.left ⁻¹ᵁ U) ((T.left.app U).hom f)
    (by rw [← top_le_preimage_comp, hT, neg_add_cancel]; exact h)
  simp only [valAt'_comp, hT] at h1
  rw [fderiv_comp_add_left (f := fun z => valAt' (u.ex z).left U f), neg_add_cancel] at h1
  exact h1

variable {D : ℕ} (c : AlgChart A.hom (RingHom.id ℂ) D)

theorem isOpen_pre_source : IsOpen (pt u ⁻¹' c.e.source) := c.e.open_source.preimage (continuous_pt u)

theorem analyticOnNhd_chart : AnalyticOnNhd ℂ (c.e ∘ pt u) (pt u ⁻¹' c.e.source) :=
  SCV.analyticOnNhd_of_differentiableOn (isOpen_pre_source u c) (differentiableOn_euclidean.2 fun a =>
    ((differentiableOn_ev u _ (c.x a)).mono fun _ hz => c.source_subset hz).congr fun _ hz => c.apply_eq _ hz a)

theorem injective_fderiv {z₀ : Fin g → ℂ} (hz : pt u z₀ ∈ c.e.source) :
    Function.Injective (fderiv ℂ (c.e ∘ pt u) z₀) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => eq_zero_of_fderiv_eq_zero u z₀ w fun U f hU => ?_
  have e : ev _ _ U f ∘ pt u =ᶠ[𝓝 z₀] (ev _ _ U f ∘ c.e.symm) ∘ (c.e ∘ pt u) :=
    eventually_of_mem ((isOpen_pre_source u c).mem_nhds hz) fun z hz =>
      (congrArg (ev _ _ U f) (c.e.left_inv hz)).symm
  change fderiv ℂ (ev _ _ U f ∘ pt u) z₀ w = 0
  rw [e.fderiv_eq, fderiv_comp (f := c.e ∘ pt u) z₀ (c.differentiableAt_ev f hz hU)
    (analyticOnNhd_chart u c z₀ hz).differentiableAt, ContinuousLinearMap.comp_apply, hw, map_zero]

theorem dim_le {z₀ : Fin g → ℂ} (hz : pt u z₀ ∈ c.e.source) : D ≤ g := by
  have h1 : dimH ((c.e ∘ pt u) '' (pt u ⁻¹' c.e.source)) ≤ dimH (pt u ⁻¹' c.e.source) :=
    dimH_image_le_of_locally_lipschitzOn fun z hz => by
      obtain ⟨K, t, ht, h⟩ := (analyticOnNhd_chart u c z hz).contDiffAt.exists_lipschitzOnWith
      exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, h⟩
  rw [Set.image_comp, Set.image_preimage_eq _ (pt_surjective u), c.e.image_source_eq_target,
    Real.dimH_of_mem_nhds (c.e.open_target.mem_nhds (c.e.map_source hz)),
    Real.dimH_of_mem_nhds ((isOpen_pre_source u c).mem_nhds hz), Nat.cast_le,
    finrank_real_of_complex, finrank_real_of_complex] at h1
  simpa using h1

theorem holoOn_of_comp (R : AnRead A.hom (RingHom.id ℂ) D) {S : Set (CxPts A.hom (RingHom.id ℂ))} (hS : IsOpen S)
    {F : CxPts A.hom (RingHom.id ℂ) → ℂ} (hF : DifferentiableOn ℂ (F ∘ pt u) (pt u ⁻¹' S)) : R.HoloOn S F := by
  intro i v hv
  set c := R.chart i
  obtain ⟨z₀, hz₀⟩ := pt_surjective u (c.e.symm v)
  have hz : pt u z₀ ∈ c.e.source := hz₀ ▸ c.e.map_target hv.1
  have hv₀ : (c.e ∘ pt u) z₀ = v := by rw [Function.comp_apply, hz₀, c.e.right_inv hv.1]
  have hinj := injective_fderiv u c hz
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv ℂ (c.e ∘ pt u) z₀ : (Fin g → ℂ) →ₗ[ℂ] V D)) hinj
  have hrk : Module.finrank ℂ (Fin g → ℂ) = Module.finrank ℂ (V D) :=
    le_antisymm hle (by simpa using dim_le u c hz)
  let L : (Fin g → ℂ) ≃L[ℂ] V D := (LinearEquiv.ofBijective
    (fderiv ℂ (c.e ∘ pt u) z₀ : (Fin g → ℂ) →ₗ[ℂ] V D)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).1 hinj⟩).toContinuousLinearEquiv
  have hs : HasStrictFDerivAt (c.e ∘ pt u) (L : (Fin g → ℂ) →L[ℂ] V D) z₀ :=
    (analyticOnNhd_chart u c z₀ hz).hasStrictFDerivAt
  have hd := hs.to_localInverse.hasFDerivAt.differentiableAt
  have hr := hs.eventually_right_inverse
  have hl := hs.localInverse_apply_image
  have ht := hs.localInverse_tendsto
  rw [hv₀] at hd hr hl ht
  have hFz : DifferentiableAt ℂ (F ∘ pt u) (hs.localInverse _ _ _ v) := by
    rw [hl]
    exact hF.differentiableAt ((hS.preimage (continuous_pt u)).mem_nhds (show pt u z₀ ∈ S from hz₀ ▸ hv.2))
  refine ((hFz.comp v hd).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hr, ht ((isOpen_pre_source u c).mem_nhds hz)] with w hw hw'
  exact congrArg F ((congrArg c.e.symm hw.symm).trans (c.e.left_inv hw'))

theorem exists_isFn (hA : IsAbelianScheme A) (hp : IsProjOver A.hom) (hM : M.IsLB) {θ : (Fin g → ℂ) → ℂ}
    (hθ : Differentiable ℂ θ)
    (hper : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) :
    ∃ s : M.Sec, u.IsFn s θ := by
  classical
  obtain ⟨D, hD⟩ := AbelianDim.exists_relDim ℂ A hA
  let r := Function.surjInv (pt_surjective u)
  have hr : ∀ y, pt u (r y) = y := Function.surjInv_eq (pt_surjective u)
  let s : M.ι → CxPts A.hom (RingHom.id ℂ) → ℂ := fun i y =>
    if y ∈ ptsIn _ _ (M.U i) then θ (r y) * u.fr i (r y) else 0
  have hs : ∀ i z, pt u z ∈ ptsIn _ _ (M.U i) → s i (pt u z) = θ z * u.fr i z := fun i z hz => by
    have := hper _ (sub_mem_of_pt_eq u (hr (pt u z))) i z hz
    rw [add_sub_cancel] at this
    exact (if_pos hz).trans this
  have hmem : s ∈ (AnRead.all A.hom (RingHom.id ℂ) D).holSec M := by
    refine ⟨⟨fun i j y hi hj => ?_, fun i y h => if_neg h⟩, fun i => holoOn_of_comp u _ (isOpen_ptsIn _) ?_⟩
    · obtain ⟨z, rfl⟩ := pt_surjective u y
      have hij : pt u z ∈ ptsIn _ _ (M.U i ⊓ M.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
      have e : u.fr i z = gv _ _ M i j (pt u z) * u.fr j z := u.fr_compat i j z hij
      rw [hs i z hi, hs j z hj, e, mul_left_comm]
    · exact (hθ.differentiableOn.mul (u.fr_hol i)).congr fun z hz => hs i z hz
  obtain ⟨σ, hσ⟩ := (GlobalTheory.Published.serreHolomorphicSections_holds A.left A.hom D hD hp _ M hM).2 ⟨s, hmem⟩
  exact ⟨σ, fun i z hz => (congrFun₂ (congrArg Subtype.val hσ) i (pt u z)).trans (hs i z hz)⟩

theorem isUnit_of_ev_ne_zero {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] {U : Y.Opens} (f : Γ(Y, U))
    (h : ∀ y ∈ ptsIn p (RingHom.id ℂ) U, ev p _ U f y ≠ 0) : IsUnit f := by
  have := LocallyOfFiniteType.jacobsonSpace p
  have hU : U ≤ Y.basicOpen f := by
    by_contra hn
    obtain ⟨x, hx, hx'⟩ := Set.not_subset.1 hn
    obtain ⟨y, hy, hy'⟩ := nonempty_inter_closedPoints (Z := (U : Set Y) ∩ (Y.basicOpen f : Set Y)ᶜ) ⟨x, hx, hx'⟩
      (U.isOpen.isLocallyClosed.inter (Y.basicOpen f).isOpen.isClosed_compl.isLocallyClosed)
    let q : CxPts p (RingHom.id ℂ) :=
      ⟨pointOfClosedPoint p y hy', (pointOfClosedPoint_comp p y hy').trans (Spec.map_id _).symm⟩
    have hq : q.1 (IsLocalRing.closedPoint ℂ) = y := pointOfClosedPoint_apply p y hy' _
    have hqU : q ∈ ptsIn p _ U := mem_ptsIn.2 (hq ▸ hy.1)
    exact hy.2 (hq ▸ mem_ptsIn.1 ((mem_ptsIn_basicOpen hqU f).2 (h q hqU)))
  exact Y.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => (Y.mem_basicOpen f x hx).1 (hU hx)

theorem hasGen_of_periodic : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M : LB A.left), M.IsLB → ∀ (g : ℕ) (u : HolUnif A M g) (θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ →
    (∀ z, θ z ≠ 0) →
    (∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) →
    HasGen M := by
  intro A _ hA hp M hM g u θ hθ h0 hper
  obtain ⟨s, hs⟩ := exists_isFn u hA hp hM hθ hper
  have := hA.proper
  have hu : ∀ i, IsUnit (s.f i) := fun i => isUnit_of_ev_ne_zero A.hom _ fun y hy => by
    obtain ⟨z, rfl⟩ := pt_surjective u y
    exact (hs i z hy).trans_ne (mul_ne_zero (h0 z) (u.fr_ne i z hy))
  exact ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j)⟩

end GlobalTheory.HolUnifSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftSectionsOneLevel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg

theorem glue_chart {X X' : Scheme.{0}} (φ : X' ⟶ X) {M L' : LB X} {L : LB X'} (ω : LB.Iso L' M)
    (hω : ω.IsGen) (u : LB.Iso L (L'.pull φ)) (hu : PGen u) (hM : M.IsLB) (hL' : L'.IsLB) (hL : L.IsLB)
    (σ : LB.Sec L) (i : M.ι) :
    ∃ a : Γ(X', φ ⁻¹ᵁ M.U i), ∀ z b c, φ z ∈ M.U i → φ z ∈ L'.U b → z ∈ L.U c →
      gs (𝟙 _) z _ a = (gv ω φ z i b).val * ((gw u (𝟙 _) z b c).val * gs (𝟙 _) z _ (σ.f c)) := by
  let W : L'.ι × L.ι → X'.Opens := fun p => φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1) ⊓ L.U p.2
  have l₀ : ∀ p, W p ≤ φ ⁻¹ᵁ M.U i := fun p x hx => hx.1.1
  have l₁ : ∀ p, W p ≤ φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1) := fun p x hx => hx.1
  have l₂ : ∀ p, W p ≤ (L'.pull φ).U (fun _ => p.1) ⊓ L.U p.2 := fun p x hx => ⟨mem_pull.2 hx.1.2, hx.2⟩
  have l₃ : ∀ p, W p ≤ L.U p.2 := fun p x hx => hx.2
  have key : ∀ (y : X') (b b' : L'.ι) (c c' : L.ι), φ y ∈ M.U i → φ y ∈ L'.U b → φ y ∈ L'.U b' →
      y ∈ L.U c → y ∈ L.U c' →
      (gv ω φ y i b).val * ((gw u (𝟙 _) y b c).val * gs (𝟙 _) y _ (σ.f c)) =
        (gv ω φ y i b').val * ((gw u (𝟙 _) y b' c').val * gs (𝟙 _) y _ (σ.f c')) := by
    intro y b b' c c' hi hb hb' hc hc'
    have h1 := gm_isGen hω φ y i i b b' hi hi hb hb'
    have h2 := hu X' (𝟙 _) y b b' c c' hb hb' hc hc'
    have h3 := GlobalTheory.SecPullIso.gs_sec_trans σ (𝟙 _) y hc hc'
    rw [gm_self hM φ y hi, one_mul] at h1
    rw [Category.id_comp] at h2
    rw [h1, h2, h3]
    generalize gm φ y _ (L'.g b b') = B
    generalize gm (𝟙 X') y _ (L.g c c') = C
    generalize gv ω φ y i b' = D
    generalize gw u (𝟙 _) y b' c' = E
    generalize gs (𝟙 X') y _ (σ.f c') = s
    simp only [Units.val_mul]
    have hB := B.inv_mul
    have hC := C.inv_mul
    linear_combination ((D : _) * E * s * (C⁻¹ : _ˣ) * C) * hB + ((D : _) * E * s) * hC
  obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(X', W p), ∀ z p, z ∈ W p →
      gs (𝟙 _) z (W p) (v p) = (gv ω φ z i p.1).val * ((gw u (𝟙 _) z p.1 p.2).val * gs (𝟙 _) z _ (σ.f p.2)) :=
    ⟨fun p => (res (l₁ p) (pullU φ _ (ω.s (i, p.1)))).val * ((res (l₂ p) (u.s (fun _ => p.1, p.2))).val *
        (X'.presheaf.map (homOfLE (l₃ p)).op).hom (σ.f p.2)), fun z p hz => by
      rw [gs_mul _ z _ hz, gs_mul _ z _ hz, gs_unit _ z _ hz, gs_unit _ z _ hz, gm_res (𝟙 X') z (l₁ p) hz,
        show gm (𝟙 X') z (W p) (res (l₂ p) (u.s (fun _ => p.1, p.2))) = gw u (𝟙 _) z p.1 p.2 from gm_res (𝟙 X') z (l₂ p) hz _, gs_res (𝟙 X') z (l₃ p) hz, show gm (𝟙 X') z (φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1)) (pullU φ _ (ω.s (i, p.1))) = gv ω φ z i p.1 from
          (gm_pull (𝟙 _) φ z _ (l₁ p hz) _).trans (by rw [Category.id_comp]; rfl)]⟩
  obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (φ ⁻¹ᵁ M.U i) (fun p => homOfLE (l₀ p)) (fun y hy => by
      obtain ⟨b, hb⟩ := exists_chart hL' (φ y)
      obtain ⟨c, hc⟩ := exists_chart hL y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(b, c), ⟨hy, hb⟩, hc⟩) v
    (fun p q => fn_ext (V := W p ⊓ W q) fun y hy => by
      refine (gs_res (𝟙 _) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 _) y inf_le_right hy _).symm)
      rw [hv y p hy.1, hv y q hy.2]
      exact key y p.1 q.1 p.2 q.2 hy.1.1.1 hy.1.1.2 hy.2.1.2 hy.1.2 hy.2.2)
  refine ⟨a, fun z b c h₁ h₂ h₃ => ?_⟩
  have hz : z ∈ W (b, c) := ⟨⟨h₁, h₂⟩, h₃⟩
  exact (gs_res (𝟙 _) z (l₀ (b, c)) hz a).symm.trans ((congrArg (gs (𝟙 _) z (W (b, c))) (ha (b, c))).trans
    (hv z (b, c) hz))

theorem lift_step : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ (L : LB (Y e).left) (L' : LB (Y (e + 1)).left) (u : LB.Iso L (L'.pull (β e))), L.IsLB → L'.IsLB → u.IsGen → LBIso (L'.pull (γ (e + 1))) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ : LB.Sec L, ∃ σ' : LB.Sec L', Rel (β e) u σ' σ := by
  intro R _ I Y β hβ n C H₀ s₀ hH₀ hs₀ γ hγ0 hγ e k hc L L' u hL hL' hu hpw σ
  obtain ⟨g, hMLB, ⟨ω, hω⟩, hcong⟩ := _root_.GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull R I Y β hβ n C H₀ s₀ hH₀ hs₀ γ hγ0 hγ (e + 1) k L' hL' hpw
  have hup : PGen u := (isGen_iff u).1 hu
  choose σi hσi using fun i => glue_chart (M := (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left)) (β e) ω hω u
    hup hMLB hL' hL σ i
  have hcoc : ∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j →
      gs (𝟙 _) z _ (σi i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σi j) := by
    intro z i j hi hj
    obtain ⟨b, hb⟩ := exists_chart hL' (β e z)
    obtain ⟨c, hc'⟩ := exists_chart hL z
    rw [hσi i z b c hi hb hc', hσi j z b c hj hb hc']
    have h1 := gm_isGen hω (β e) z i j b b hi hj hb hb
    rw [gm_self hL' (β e) z hb, inv_one, mul_one] at h1
    rw [h1, gs_unit (β e) z (C.D (e + 1) i ⊓ C.D (e + 1) j) ⟨hi, hj⟩, Units.val_mul, mul_assoc]
  obtain ⟨σ'', hσ''⟩ := _root_.GlobalTheory.FormalAlg.lift_cech R I Y β hβ n C e k hc g hMLB hcong σi hcoc
  let w := isoPullId ω (F := 𝟙 _) rfl
  have hw : w.IsGen := (isGen_iff w).2 (isoPullId_pgen hω rfl)
  obtain ⟨σ', hσ'⟩ := GlobalTheory.SecPullIso.exists_pull (𝟙 _) _ L' w hMLB hL' hw σ''
  refine ⟨σ', fun z b c hb hc' => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart hMLB (β e z)
  have hR : Rel (𝟙 _) w σ'' σ' := hσ'
  have e1 := hR.pull (β e) z i b hi hb
  rw [Category.comp_id, gw_isoPullId ω rfl (β e) z i b hi hb] at e1
  have e2 : gs (β e) z _ (σ''.f i) = gs (𝟙 _) z _ (σi i) := by
    rw [← hσ'' i, gs_pull (𝟙 _) (β e) z _ hi, Category.id_comp]
  rw [e2, hσi i z b c hi hb hc'] at e1
  exact ((Units.mul_right_inj (gv ω (β e) z i b)).1 e1).symm

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DivDeep

open GlobalTheory.ThetaCompare

theorem torsFrame_two_levels {S : Scheme.{0}} (P : PolAV S) {T : Over S} {m M : ℕ}
    {rig rig' : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} {τ τ'} (H : IsTorsFrame P rig m x τ)
    (H' : IsTorsFrame P rig' M x τ') {y : T.left} {J} (hJ : Good P.L y J) :
    (val τ (𝟙 _) y J / val τ' (𝟙 _) y J) ^ (m ^ 2 * M ^ 2) =
      (val rig T.hom y J / val rig' T.hom y J) ^ (m ^ 2 * M ^ 2) := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P m T
  obtain ⟨β, hβ⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P M T
  have a := torsFrame_pow hG P hα H hJ
  have b := torsFrame_pow hG P hβ H' hJ
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  have rβ := Reg.two (y := y) (J := J) β hβ (snd T P.A) (snd T P.A ^ M) rfl rfl
  have c := (((rα.pow hJ (M ^ 2)).mul hJ (rβ.pull hJ (snd T P.A ^ m))).mul hJ
    ((rβ.pow hJ (m ^ 2)).mul hJ (rα.pull hJ (snd T P.A ^ M))).inv).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, ← pow_mul, mul_comm M m]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) x 1
  simp only [SymLiftOdd.comp_pow', pt_snd, H.1, H'.1, one_pow] at c
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div] at a b c ⊢
  linear_combination (norm := module) (M ^ 2) • a - (m ^ 2) • b + c

theorem exists_cst {K : Type} [Field K] (z : Sp K) : ∃ c : K →+* (Sp K).presheaf.stalk z, Function.Injective c ∧
    ∀ a, gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = c a :=
  ⟨((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom, RingHom.injective _,
    fun _ => gs_eq (𝟙 _) z ⊤ trivial _⟩

theorem same_ratio {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ε} {ρ' : S'.Real} {ε'} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
    (h : Same ρ ε ρ' ε' lab φ) (a b : S.Gam) :
    ∃ k, 0 < k ∧ (S'.th (lab a) * φ (S.th b)) ^ k = (S'.th (lab b) * φ (S.th a)) ^ k := by
  obtain ⟨P₀, f, f', -, gp, gp', lb, lb', -, hw⟩ := h
  choose w hw hw' using hw
  have hs : ∀ x, w x ≫ P₀.A.hom = 𝟙 _ := fun x => by
    have e : (w x ≫ P₀.A.hom) ≫ spMap S'.R.val.toRingHom = 𝟙 _ ≫ spMap S'.R.val.toRingHom := by
      rw [Category.assoc, ← gp'.1.w, ← Category.assoc, hw', Category.assoc, Over.w, Category.id_comp]
      exact Category.comp_id _
    haveI : IsFractionRing S'.R Ω' := IsFractionRing.of_field _ _ fun x => by
      obtain ⟨a, ha, b, hb, e⟩ := S'.frac x
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
    haveI : IsPreimmersion (spMap S'.R.val.toRingHom) :=
      IsPreimmersion.of_isLocalization (R := S'.R) (S := Ω') (nonZeroDivisors S'.R)
    exact (cancel_mono _).1 e
  let x : S.Gam → (baseOver (Sp Ω') ⟶ P₀.A) := fun a => Over.homMk (w a) (hs a)
  obtain ⟨rig, τ, -, hτ, ht⟩ := FrameMove.exists_move (T := baseOver (Sp S.R)) (T' := baseOver (Sp Ω'))
    (h := spMap (φ.comp S.R.val.toRingHom)) gp lb ((Category.comp_id _).trans (Category.id_comp _).symm) ρ.rig_gen
    (x := ρ.pt) (x' := x) hw ρ.fr_tors
  obtain ⟨rig', τ', -, hτ', ht'⟩ := FrameMove.exists_move (T := baseOver (Sp S'.R)) (T' := baseOver (Sp Ω'))
    (h := spMap S'.R.val.toRingHom) gp' lb' ((Category.comp_id _).trans (Category.id_comp _).symm) ρ'.rig_gen
    (x := fun a => ρ'.pt (lab a)) (x' := x) hw' (fun a => ρ'.fr_tors (lab a))
  obtain ⟨t, ht⟩ := ht 1 ρ.th₁
  obtain ⟨t', ht'⟩ := ht' 1 ρ'.th₁
  let z : Sp Ω' := IsLocalRing.closedPoint Ω'
  obtain ⟨V, hV, hθ⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny P₀ z
  obtain ⟨θ, hθ⟩ := hθ Ω' (𝟙 _) (by rintro _ ⟨v, rfl⟩; rw [Subsingleton.elim v z]; exact hV)
  obtain ⟨r, hr⟩ := hθ t
  obtain ⟨r', hr'⟩ := hθ t'
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' (Z := (baseOver (Sp Ω')).left) P₀.isLB z
  obtain ⟨c, hc, hcv⟩ : ∃ c : Ω' →+* (baseOver (Sp Ω')).left.presheaf.stalk z, Function.Injective c ∧
      ∀ a, gs (𝟙 (Sp Ω')) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom a) = c a := exists_cst z
  have pf : ∀ {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
      (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))),
      powFrame A L x τ 1 = τ := fun x τ => congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))
  have v : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r * sval (L := P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left)
      (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (φ (S.th a)) * (val (τ a) (𝟙 _) z J).val := fun a => by
    have e := (sval_smul hr (x a) hJ).symm.trans (ht a _ (by rw [pf]; exact ρ.th_val a) z J hJ)
    rw [pf] at e
    exact e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))
  have v' : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r' * sval (L := P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left)
      (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (S'.th (lab a)) * (val (τ' a) (𝟙 _) z J).val := fun a => by
    have e := (sval_smul hr' (x a) hJ).symm.trans (ht' a _ (by rw [pf]; exact ρ'.th_val (lab a)) z J hJ)
    rw [pf] at e
    exact e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))
  have q := (torsFrame_two_levels P₀ (hτ a) (hτ' a) hJ).trans (torsFrame_two_levels P₀ (hτ b) (hτ' b) hJ).symm
  have p₁ : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have p₂ : 0 < S'.r * S'.N := Nat.mul_pos S'.r_pos (by have := S'.N_ge; omega)
  refine ⟨(S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2, by positivity, hc ?_⟩
  generalize (S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2 = k at q
  have va := v a
  have vb := v b
  have va' := v' a
  have vb' := v' b
  generalize val (τ a) (𝟙 _) z J = ua at *
  generalize val (τ b) (𝟙 _) z J = ub at *
  generalize val (τ' a) (𝟙 _) z J = ua' at *
  generalize val (τ' b) (𝟙 _) z J = ub' at *
  have e : c (S'.th (lab a) * φ (S.th b)) * (ua' * ub).val = c (S'.th (lab b) * φ (S.th a)) * (ub' * ua).val := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm, ← va', ← vb, _root_.mul_mul_mul_comm (c _), ← vb', ← va]
    ring
  have q' : (ua' * ub) ^ k = (ub' * ua) ^ k := by
    apply Additive.ofMul.injective
    replace q := congrArg Additive.ofMul q
    simp only [ofMul_mul, ofMul_pow, ofMul_div] at q ⊢
    linear_combination (norm := module) -q
  have e' := congrArg (· ^ k) e
  simp only [mul_pow, ← Units.val_pow_eq_pow_val, q'] at e'
  rw [map_pow, map_pow]
  exact (Units.mul_left_inj _).1 e'

end GlobalTheory.Poinc.DivDeep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilyKernelExactIsClopenGeometric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.KerClopen

variable {S : Scheme.{0}}

theorem comp_zsmul {L : Type} [AddCommGroup L] {G T T' : Over S} [GrpObj G] (e : L → (T ⟶ G))
    (he : ∀ a c, e (a + c) = e a * e c) (h : T' ⟶ T) (n : ℤ) (a : L) : h ≫ e (n • a) = (h ≫ e a) ^ n := by
  let φ : Multiplicative L →* (T' ⟶ G) :=
    MonoidHom.mk' (fun x => h ≫ e x.toAdd) fun x y => by
      change h ≫ e (x.toAdd + y.toAdd) = _
      rw [he, MonObj.comp_mul]
  exact map_zpow φ (Multiplicative.ofAdd a) n

theorem loc_one (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G) (M : ℕ)
    (hM : IsUnit (M : Γ(S, ⊤))) {L : Type} [AddCommGroup L] (Z : Over S) (e : L → (Z ⟶ G))
    (he : ∀ a c, e (a + c) = e a * e c) (hM' : ∀ a, e a ^ M = 1) (a : L) :
    GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x =>
      (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1) := by
  obtain ⟨Z₁, et, R⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom S G M ℤ hG hM
  have hx : ∀ n m : ℤ, e ((n + m) • a) = e (n • a) * e (m • a) := fun n m => by rw [add_smul, he]
  have hx' : ∀ n : ℤ, e (n • a) ^ M = 1 := fun n => hM' _
  have R' : GlobalTheory.LevCover.RepTors G M ℤ Z₁ et := R
  have C := GlobalTheory.LevCover.RepTors.clopenCond (T := Z) R' (fun n : ℤ => e (n • a)) (fun _ => 1) hx hx'
    (fun _ _ => (_root_.mul_one _).symm) (fun _ => one_pow _)
  obtain ⟨U, hU, H⟩ := C
  refine ⟨(U : Set Z.left), ⟨hU, U.isOpen⟩, fun k _ _ x => ?_⟩
  rw [← GlobalTheory.HkClopen.range_subset_iff x]
  have := (H (Over.mk (x ≫ Z.hom)) (Over.homMk x rfl)).symm
  refine this.trans ⟨fun h1 => ?_, fun h1 n => ?_⟩
  · have := h1 1
    rwa [one_smul, MonObj.comp_one] at this
  · rw [MonObj.comp_one, comp_zsmul e he, h1, one_zpow]

end GlobalTheory.KerClopen

open GlobalTheory.KerClopen in
theorem GlobalTheory.kerClopen_geom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (M h : ℕ), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∀ (Z : Over S) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ G)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ a, (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1 ↔ ∃ c, a = M • c) := by
  intro S G _ _ hG M h hM0 hM Z e he hM'
  let L := Fin h ⊕ Fin h → ℤ
  obtain ⟨κ, _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod L hM0
  let I₀ := Set.range q
  let r : I₀ → L := fun i => i.2.choose
  have hr : ∀ i : I₀, q (r i) = i.1 := fun i => i.2.choose_spec
  have hP : ∀ a c : L, e (a + M • c) = e a := fun a c => by
    rw [he, GlobalTheory.LevCover.add_map_nsmul he, hM', _root_.mul_one]
  have hQ : ∀ a c : L, (∃ d, a + M • c = M • d) ↔ ∃ d, a = M • d := fun a c =>
    ⟨fun ⟨d, hd⟩ => ⟨d - c, by rw [smul_sub, ← hd, add_sub_cancel_right]⟩,
     fun ⟨d, hd⟩ => ⟨d + c, by rw [hd, smul_add]⟩⟩
  have Lc := GlobalTheory.HkClopen.Loc.comb (I₀ := I₀)
    (fun i => loc_one G hG M hM Z e he hM' (r i)) fun f => ∀ i, (f i ↔ ∃ c, r i = M • c)
  refine Lc.congr fun k _ _ x => ⟨fun H a => ?_, fun H i => H (r i)⟩
  obtain ⟨c, hc⟩ := hq (r ⟨q a, a, rfl⟩) a (hr _)
  have := H ⟨q a, a, rfl⟩
  beta_reduce at this
  revert this hc
  generalize r ⟨q a, a, rfl⟩ = a₀
  intro hc this
  subst hc
  rw [hP, hQ]
  exact this
end
end

