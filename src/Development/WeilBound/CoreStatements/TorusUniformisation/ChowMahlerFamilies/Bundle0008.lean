module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionOnConnectedFibreUnit
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.FibreFunctionConstant

theorem exists_section_of_germs (Y : Scheme.{0}) (g : ∀ y : Y, Y.presheaf.stalk y)
    (hg : ∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (t : Γ(Y, W)),
      ∀ z (hz : z ∈ W), Y.presheaf.germ W z hz t = g z) :
    ∃ a : Γ(Y, ⊤), ∀ y, Y.presheaf.germ ⊤ y trivial a = g y := by
  choose W hW t ht using hg
  have compat : TopCat.Presheaf.IsCompatible Y.sheaf.obj W t := by
    intro i j
    apply TopCat.Presheaf.section_ext Y.sheaf (W i ⊓ W j)
    rintro y ⟨hi, hj⟩
    exact (TopCat.Presheaf.germ_res_apply Y.presheaf
      (TopologicalSpace.Opens.infLELeft (W i) (W j)) y ⟨hi, hj⟩ (t i)).trans
      ((ht i y hi).trans ((ht j y hj).symm.trans
        (TopCat.Presheaf.germ_res_apply Y.presheaf
          (TopologicalSpace.Opens.infLERight (W i) (W j)) y ⟨hi, hj⟩ (t j)).symm))
  have hcov : (⊤ : Y.Opens) ≤ iSup W := fun y _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hcov t compat
  refine ⟨a, fun q => ?_⟩
  have e := TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (le_top : W q ≤ ⊤)) q (hW q) a
  have e2 : (Y.presheaf.map (homOfLE (le_top : W q ≤ ⊤)).op).hom a = t q := ha q
  exact e.symm.trans ((congrArg (fun z => (Y.presheaf.germ (W q) q (hW q)).hom z) e2).trans (ht q q (hW q)))

theorem unit_of_cover {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hc : IsCptGen ξ)
    (π : Γ(X, ⊤)) (ϖ : Ω) (h0 : ϖ ≠ 0)
    (hπ : ∀ p : Cpt ξ, genMap ξ p (X.presheaf.germ ⊤ p.1 trivial π) = ϖ)
    (k : Type) [Field k] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f]
    [ConnectedSpace Y] (ι : Y ⟶ X) (hι : ι.appTop π = 0) (hr : Set.range ι = zeroSet ξ ϖ)
    (h : Cpt ξ → Ω)
    (H : ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      h p ∈ regAt ξ q ∧ (h p - h q) / ϖ ∈ regAt ξ q)
    (hex : ∃ p, ¬ unitAt ξ p ϖ ∧ unitAt ξ p (h p)) : ∀ p, ¬ unitAt ξ p ϖ → unitAt ξ p (h p) := by
  have hy : ∀ y : Y, ι y ∈ zeroSet ξ ϖ := fun y => hr ▸ ⟨y, rfl⟩
  choose hs hn using hy
  have hreg : ∀ y : Y, ∃ c : X.presheaf.stalk (ι y), genMap ξ ⟨ι y, hs y⟩ c = h ⟨ι y, hs y⟩ := fun y => by
    obtain ⟨U, hU, HU⟩ := H ⟨ι y, hs y⟩ (hn y)
    exact (HU _ hU (hn y)).1
  choose c hcv using hreg
  have hzero : ∀ y : Y, (ι.stalkMap y).hom (X.presheaf.germ ⊤ (ι y) trivial π) = 0 := fun y => by
    have := Scheme.Hom.germ_stalkMap_apply ι ⊤ y trivial π
    rw [this]
    have e : (ι.app ⊤).hom π = 0 := hι
    erw [e]
    exact map_zero _
  obtain ⟨a, ha⟩ := exists_section_of_germs Y (fun y => (ι.stalkMap y).hom (c y)) (fun y => by
    obtain ⟨U, hU, HU⟩ := H ⟨ι y, hs y⟩ (hn y)
    obtain ⟨W, hW, t, ht⟩ := X.presheaf.exists_germ_eq (c y)
    refine ⟨ι ⁻¹ᵁ (W ⊓ U), ⟨hW, hU⟩, ι.app (W ⊓ U) (X.presheaf.map (homOfLE inf_le_left).op t), fun z hz => ?_⟩
    have hz' : ι z ∈ W ⊓ U := hz
    rw [← Scheme.Hom.germ_stalkMap_apply ι (W ⊓ U) z hz']
    have e1 := TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE inf_le_left : W ⊓ U ⟶ W) (ι z) hz' t
    erw [e1]
    obtain ⟨d, hd⟩ := (HU ⟨ι z, hs z⟩ hz'.2 (hn z)).2
    have e2 : genMap ξ ⟨ι z, hs z⟩ (X.presheaf.germ W (ι z) hz'.1 t) = h ⟨ι y, hs y⟩ := by
      rw [← hcv y, ← ht]
      exact genMap_germ_eq_genMap_germ ξ W ⟨ι z, hs z⟩ ⟨ι y, hs y⟩ hz'.1 hW t
    have e3 : X.presheaf.germ W (ι z) hz'.1 t = c z + X.presheaf.germ ⊤ (ι z) trivial π * d := by
      apply hc.inj ⟨ι z, hs z⟩
      have e4 := hπ ⟨ι z, hs z⟩
      refine e2.trans ?_
      rw [map_add (f := _), map_mul]
      erw [hcv z, e4, hd]
      field_simp
      ring
    erw [e3]
    rw [map_add (f := _), map_mul, hzero, zero_mul, add_zero])
  have hiff : ∀ y : Y, y ∈ Y.basicOpen a ↔ unitAt ξ ⟨ι y, hs y⟩ (h ⟨ι y, hs y⟩) := fun y => by
    rw [Scheme.mem_basicOpen_top]
    erw [ha y]
    rw [isUnit_map_iff]
    refine Iff.trans ?_ (unitAt_iff_of_isCptGen ξ hc ⟨ι y, hs y⟩ _).symm
    constructor
    · intro hu
      exact ⟨c y, hu, hcv y⟩
    · rintro ⟨u, hu, e⟩
      rwa [← hc.inj ⟨ι y, hs y⟩ (e.trans (hcv y).symm)]
  have lift : ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ y : Y, p = ⟨ι y, hs y⟩ := fun p hp => by
    obtain ⟨y, hy⟩ : p.1 ∈ Set.range ι := hr ▸ (coe_mem_zeroSet p).2 hp
    exact ⟨y, Subtype.ext hy.symm⟩
  obtain ⟨p₀, hp₀, hu₀⟩ := hex
  obtain ⟨y₀, rfl⟩ := lift p₀ hp₀
  have hu := isUnit_of_basicOpen_nonempty_of_universallyClosed k Y f a ⟨y₀, (hiff y₀).2 hu₀⟩
  intro p hp
  obtain ⟨y, rfl⟩ := lift p hp
  refine (hiff y).1 ?_
  rw [Y.basicOpen_of_isUnit hu]
  trivial

end PositivityTheory.Xgn.FibreFunctionConstant

open PositivityTheory.Xgn.FibreFunctionConstant in
theorem PositivityTheory.Xgn.function_on_connected_fibre_unit : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hc hconn h H hex
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨U, hU, hUc, -⟩ := cpt_open_integral X Ω ξ hc
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by simpa using hUc)
  let r : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  haveI : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective (R := O))
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hrr : ∀ x : Spec (CommRingCat.of O), x ∈ Set.range r ↔ ϖ ∈ x.asIdeal := fun x => by
    have e : Set.range r = PrimeSpectrum.zeroLocus (RingHom.ker (IsLocalRing.residue O) : Set O) :=
      range_comap_of_surjective _ _ (IsLocalRing.residue_surjective (R := O))
    rw [e, IsLocalRing.ker_residue, hmax, PrimeSpectrum.zeroLocus_span]
    exact Set.singleton_subset_iff
  let ι : pullback (U.ι ≫ s) r ⟶ X := pullback.fst _ _ ≫ U.ι
  have hr : Set.range ι = zeroSet ξ (algebraMap O Ω ϖ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : genPt ξ ⤳ ι y := (hU _).1 (pullback.fst (U.ι ≫ s) r y).2
      refine ⟨h1, ?_⟩
      rw [(ConstReg.regular_const X Ω ξ O s hs ⟨_, h1⟩ ϖ).2 hc, not_not, ← hrr]
      refine ⟨pullback.snd (U.ι ≫ s) r y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]
      simp [ι]
    · rintro ⟨h1, h2⟩
      rw [(ConstReg.regular_const X Ω ξ O s hs ⟨_, h1⟩ ϖ).2 hc, not_not, ← hrr] at h2
      have h3 : (⟨x, (hU x).2 h1⟩ : U.toScheme) ∈ Set.range (pullback.fst (U.ι ≫ s) r) := by
        rw [Scheme.Pullback.range_fst]
        exact h2
      obtain ⟨y, hy⟩ := h3
      refine ⟨y, ?_⟩
      simp [ι, hy]
  haveI : ConnectedSpace (pullback (U.ι ≫ s) r : Scheme.{0}) := by
    rw [← hr, ← Set.image_univ] at hconn
    rw [connectedSpace_iff_univ]
    exact ⟨hconn.1.of_image, ι.isEmbedding.isInducing.isPreconnected_image.1 hconn.2⟩
  refine unit_of_cover ξ hc (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) _
    ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) (fun p => ConstReg.genMap_germ_const ξ s hs p ϖ)
    (IsLocalRing.ResidueField O) _ (pullback.snd (U.ι ≫ s) r) ι ?_ hr h H hex
  have e : ι ≫ s = pullback.snd (U.ι ≫ s) r ≫ r := by
    rw [← pullback.condition]; simp [ι]
  have e1 : r.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) = 0 := by
    have h3 := congrArg (fun q => q.hom ϖ)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))
    have h3' : (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField O))).inv.hom (IsLocalRing.residue O ϖ) =
      r.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ) := h3
    rw [← h3', (IsLocalRing.residue_eq_zero_iff ϖ).2 (hmax ▸ Ideal.mem_span_singleton_self ϖ), map_zero]
  have e2 : (ι ≫ s).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) = 0 := by
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e1, map_zero]
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at e2
  exact e2
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ImageLatticeBaseChange
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.ImageLatticeBaseChange

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem mem_stdLat (R : Subalgebra o Ω) {ι : Type} (v : ι → Ω) :
    v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem isBaseChange_bcMap (C : Type) [Field C] [Algebra Ω C] (m : ℕ) :
    IsBaseChange C (bcMap Ω C (Fin m)) :=
  IsBaseChange.finitePow (Fin m) (IsBaseChange.linearMap Ω C)

theorem locFree_div (R : Subalgebra o Ω) {m : ℕ} {w : Ω} (hw : w ≠ 0)
    (L : AddSubgroup (Fin m → Ω)) (hL : ∀ v, v ∈ L ↔ ∀ i, w * v i ∈ R) : LocFree R m L := by
  have hb : ∀ a : Fin m → Ω, (∑ q, a q • w⁻¹ • (Pi.single q 1 : Fin m → Ω)) = fun i => a i * w⁻¹ := by
    intro a
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨?_, 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem, by simp,
    fun _ => ⟨fun q => w⁻¹ • (Pi.single q 1 : Fin m → Ω), ?_, ?_, ?_⟩⟩
  · intro a ha e he
    rw [hL] at he ⊢
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm]
    exact R.mul_mem ha (he i)
  · have h := (Pi.basisFun Ω (Fin m)).linearIndependent.map'
      (LinearEquiv.smulOfNeZero Ω (Fin m → Ω) w⁻¹ (inv_ne_zero hw)).toLinearMap
      (LinearEquiv.ker _)
    simpa [Function.comp_def] using h
  · rw [Submodule.eq_top_iff']
    intro x
    have hx : x = ∑ q, (w * x q) • (w⁻¹ • (Pi.single q 1 : Fin m → Ω)) := by
      rw [hb (fun q => w * x q)]
      funext i
      field_simp
    rw [hx]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  · intro e
    constructor
    · rintro ⟨k, hk⟩
      simp only [one_pow, one_smul] at hk
      refine ⟨fun q => w * e q, fun q => ⟨0, by simpa using (hL e).1 hk q⟩, ?_⟩
      rw [hb]
      funext i
      field_simp
    · rintro ⟨a, ha, rfl⟩
      refine ⟨0, ?_⟩
      simp only [pow_zero, one_smul]
      rw [hb, hL]
      intro i
      obtain ⟨k, hk⟩ := ha i
      simp only [one_pow, one_mul] at hk
      field_simp
      exact hk

end PositivityTheory.Xgn.ImageLatticeBaseChange

private theorem dotDual_spanOver_bcMap_eq {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
    {m k : ℕ} (A : AddSubgroup (Fin m → Ω)) (a γ : Fin k → Fin m → Ω) (ha : ∀ i, a i ∈ A)
    (hγ : ∀ i, γ i ∈ dotDual R A) (hid : ∀ l j, ∑ i, a i l * γ i j = if l = j then 1 else 0) :
    dotDual RC (spanOver RC (bcMap Ω C (Fin m) '' A)) = spanOver RC (bcMap Ω C (Fin m) '' dotDual R A) := by
  have hb : ∀ (v : Fin m → Ω) j, bcMap Ω C (Fin m) v j = algebraMap Ω C (v j) := fun _ _ => rfl
  have hdot : ∀ u v : Fin m → Ω,
      bcMap Ω C (Fin m) u ⬝ᵥ bcMap Ω C (Fin m) v = algebraMap Ω C (u ⬝ᵥ v) := by
    intro u v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, hb, map_sum, map_mul]
  apply le_antisymm
  · intro y hy
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual] at hy
    have hy' : y = ∑ i, (bcMap Ω C (Fin m) (a i) ⬝ᵥ y) • bcMap Ω C (Fin m) (γ i) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, hb]
      calc y j = ∑ l, y l * algebraMap Ω C (if l = j then 1 else 0) := by
            simp [apply_ite]
        _ = ∑ i, (∑ l, algebraMap Ω C (a i l) * y l) * algebraMap Ω C (γ i j) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp_rw [← hid, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
            ring
    rw [hy']
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
      ⟨_, hy _ (AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨a i, ha i, rfl⟩, (one_smul _ _).symm⟩),
        _, ⟨γ i, hγ i, rfl⟩, rfl⟩
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, _, ⟨g, hg, rfl⟩, rfl⟩
    have hg' := (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual R A g).1 hg
    rw [SetLike.mem_coe, PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual]
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨d, hd, _, ⟨u, hu, rfl⟩, rfl⟩ := hv
      rw [smul_dotProduct, dotProduct_smul, hdot, smul_eq_mul, smul_eq_mul]
      exact RC.mul_mem hd (RC.mul_mem hc (hR _ (hg' u hu)))
    | zero => simp
    | add u v _ _ hu hv =>
      rw [add_dotProduct]
      exact add_mem hu hv
    | neg u _ hu =>
      rw [neg_dotProduct]
      exact neg_mem hu

private theorem exists_dual_pair_af_of_summand_locFree {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F]
    [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) (hS : Summand (D.l1 R p) (linMap n χ).range)
    (hl1 : LocFree R (Fintype.card F ^ n) (D.l1 R p)) :
    ∃ (k : ℕ) (a γ : Fin k → Fin n → Ω), (∀ i, a i ∈ D.af R p χ) ∧ (∀ i, γ i ∈ dotDual R (D.af R p χ)) ∧
      ∀ l j, ∑ i, a i l * γ i j = if l = j then 1 else 0 := by
  classical
  obtain ⟨π, hπ, hπL⟩ := PositivityTheory.Xgn.GoodLatticeBaseChange.af_retract R D p χ h0 h1 hS
  let L1 : Submodule R ((Fin n → F) → Ω) :=
    { carrier := D.l1 R p
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      smul_mem' := fun c v hv => hl1.1 c c.2 v hv }
  obtain ⟨k, φ, u, hφ, hsum⟩ := GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.exists_dualBasis (L := L1) hl1
  refine ⟨k * Fintype.card F ^ n, fun i => π (u (finProdFinEquiv.symm i)),
    fun i j => φ (finProdFinEquiv.symm i) (linMap n χ (Pi.single j 1)), ?_, ?_, ?_⟩
  · intro i
    exact hπL _ (u _).2
  · intro i
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual]
    intro v hv
    have hv' : v = ∑ j, v j • (Pi.single j 1 : Fin n → Ω) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply]
    have hval : v ⬝ᵥ (fun j => φ (finProdFinEquiv.symm i) (linMap n χ (Pi.single j 1))) =
        φ (finProdFinEquiv.symm i) (linMap n χ v) := by
      conv_rhs => rw [hv']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
    rw [hval]
    exact hφ _ _ hv
  · intro l j
    have h := congrArg (fun e => π e l) (hsum (linMap n χ (Pi.single j 1)))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hπ] at h
    rw [show (if l = j then (1 : Ω) else 0) = (Pi.single j 1 : Fin n → Ω) l by simp [Pi.single_apply], ← h]
    exact (finProdFinEquiv.symm.sum_comp
      (fun x => π (u x) l * φ x (linMap n χ (Pi.single j 1)))).trans
      (Finset.sum_congr rfl fun x _ => mul_comm _ _)

private theorem map_snd_spanOver_prodMap_eq {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C)
    {X Y Xc Yc : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Xc] [Module C Xc] [AddCommGroup Yc]
    [Module C Yc] (f : X → Xc) (g : Y → Yc) (S : AddSubgroup (X × Y)) :
    AddSubgroup.map (AddMonoidHom.snd Xc Yc) (spanOver RC (Prod.map f g '' S)) =
      spanOver RC (g '' AddSubgroup.map (AddMonoidHom.snd X Y) S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, g x.2, ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a • Prod.map f g x, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩

open PositivityTheory.Xgn.ImageLatticeBaseChange PositivityTheory.Xgn.A_graph_restrict_bc in
theorem PositivityTheory.Xgn.image_lattice_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hC hB hG hw C _ _ _ _ RC hR τ
  obtain ⟨hp, hwR, ⟨c, hc, hpc⟩, h01, hχ⟩ := hC
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hp
    rw [hpc, mul_zero]
  obtain ⟨hχ0, hχ1, hχR⟩ := hχ τ
  obtain ⟨k, a, γ, ha, hγ, hid⟩ := exists_dual_pair_af_of_summand_locFree D R p (χ τ) hχ0 hχ1 (hG.lin τ) hG.l1
  have hhh : (D.bc RC).hh RC p (fun x => algebraMap Ω C (χ τ x)) =
      spanOver RC (bcMap Ω C (Fin n) '' D.hh R p (χ τ)) := by
    unfold LieLatticeData.hh
    rw [PositivityTheory.Xgn.GoodLatticeBaseChange.af_bc R RC D p hR (χ τ) hχ0 hχ1 (hG.lin τ)]
    exact dotDual_spanOver_bcMap_eq R RC hR (D.af R p (χ τ)) a γ ha hγ hid
  have hstab : ∀ a ∈ R, ∀ v ∈ D.Del τ, a • v ∈ D.Del τ := fun a ha => (hB.stable τ a ha).2.1
  have hfst : ∀ v, v ∈ AddSubgroup.map (AddMonoidHom.fst _ _) (D.Del τ) ↔ ∀ i, w * v i ∈ R := by
    intro v
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨⟨b, c'⟩, hbc, rfl⟩
      have := ((hB.del τ).1 b).1 ⟨c', hbc⟩
      rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat] at this
      exact this
    · intro hv
      obtain ⟨c', hc'⟩ := ((hB.del τ).1 v).2 ((PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat R _).2 hv)
      exact ⟨(v, c'), hc', rfl⟩
  have hLF := PositivityTheory.Xgn.ImageLatticeBaseChange.locFree_div R hw0 _ hfst
  have hHle : D.hh R p (χ τ) ≤ AddSubgroup.map (AddMonoidHom.fst _ _) (D.Del τ) := by
    intro v hv
    rw [hfst]
    intro i
    have hv' := (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual R _ v).1 hv
    have hmem : w • (Pi.single i 1 : Fin n → Ω) ∈ D.af R p (χ τ) :=
      hw τ ⟨Pi.single i 1, (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat R _).2 (fun j => by
        by_cases h : j = i <;> simp [h, Pi.single_apply, R.one_mem, R.zero_mem]), rfl⟩
    have := hv' _ hmem
    simpa [smul_dotProduct, single_dotProduct] using this
  have hHst : ∀ a ∈ R, ∀ v ∈ D.hh R p (χ τ), a • v ∈ D.hh R p (χ τ) := by
    intro a ha v hv
    unfold LieLatticeData.hh at hv ⊢
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual] at hv ⊢
    intro u hu
    rw [dotProduct_smul, smul_eq_mul]
    exact R.mul_mem ha (hv u hu)
  have hg := (PositivityTheory.Xgn.t_graph_restrict_bc R RC hR (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ)))
    (PositivityTheory.Xgn.ImageLatticeBaseChange.isBaseChange_bcMap C n) (PositivityTheory.Xgn.ImageLatticeBaseChange.isBaseChange_bcMap C (s τ))
    (D.Del τ) (D.hh R p (χ τ)) n hstab hLF hHle hHst).1
  unfold LieLatticeData.imH
  rw [hhh]
  change AddSubgroup.map _ (spanOver RC (Prod.map (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ))) '' ↑(D.Del τ)) ⊓ _) = _
  rw [hg]
  exact map_snd_spanOver_prodMap_eq RC _ _ _
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IntegralOverPlaceDensity
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.PlaceIntegralDensity

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sheetDensity_sum {S : Type} [Fintype S] {e : ℕ} (W : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (ψ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (t : S → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) (χ : S → ((Σ k, ι k) → ℂ) → ℝ)
    (h : ∀ z ∈ mcPts W, u z = ∑ σ, t σ * χ σ z) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity W Ψ ψ u y w = ∑ σ, t σ * sheetDensity W Ψ ψ (χ σ) y w := by
  unfold sheetDensity
  split_ifs with hγ
  · rw [h _ hγ.choose_spec.2.self_of_nhds.2.1, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by ring
  · simp

theorem finsum_mem_sum {α S : Type} [Fintype S] {s : Set α} (hs : s.Finite) (t : S → ℝ) (f : S → α → ℝ) :
    ∑ᶠ w ∈ s, ∑ σ, t σ * f σ w = ∑ σ, t σ * ∑ᶠ w ∈ s, f σ w := by
  simp only [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.mul_sum]
  exact Finset.sum_comm

theorem eq_sum {Ω : Type} [Field Ω] {F : Type} [Field F] [NumberField F] {y : (Σ k, ι k) → Ω} {φ : F →+* Ω}
    {t : (F →+* ℂ) → ℝ} {u : ((Σ k, ι k) → ℂ) → ℝ} {χ : (F →+* ℂ) → ((Σ k, ι k) → ℂ) → ℝ}
    (hO : OverInt y φ) (hu : ∀ σ z, PtOver y φ σ z → u z = t σ)
    (hχ : ∀ σ, IsPlaceWeight y φ (Set.indicator {σ} 1) (χ σ)) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) : u z = ∑ σ, t σ * χ σ z := by
  obtain ⟨σ₀, hσ₀, -⟩ := existsUnique_ptOver _ _ _ _ y φ hO z hz
  rw [hu σ₀ z hσ₀, Finset.sum_eq_single σ₀]
  · rw [((hχ σ₀).near σ₀ z hσ₀).self_of_nhds]
    simp
  · intro b _ hb
    rw [((hχ b).near σ₀ z hσ₀).self_of_nhds]
    simp [Set.indicator, Ne.symm hb]
  · simp

end PositivityTheory.Xgn.PlaceIntegralDensity

open PositivityTheory.Xgn.PlaceIntegralDensity in
theorem PositivityTheory.Xgn.integral_over_place_density : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) (χ : (F →+* ℂ) → ((Σ k, ι k) → ℂ) → ℝ), OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ z, PtOver y φ σ z → u z = t σ) → (∀ σ, IsPlaceWeight y φ (Set.indicator {σ} 1) (χ σ)) → ptsIntegral W (pot L) u = ∑ σ : F →+* ℂ, t σ * ptsIntegral W (pot L) (χ σ) := by
  intro hPI K _ ι _ Ω _ F _ _ y φ W n L t u χ hO hW hA hL hu hχ
  have hmc : ∀ z ∈ mcPts W, z ∈ mcPts (mCoordIdeal y) := fun z hz => ⟨hz.1, fun f hf => hz.2 f (hW hf)⟩
  have hsum : ∀ z ∈ mcPts W, u z = ∑ σ, t σ * χ σ z := fun z hz => eq_sum hO hu hχ (hmc z hz)
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hfin := fibreFinite K ι W n hΨ.choose hA hΨ.choose_spec
    have hpt : ∀ y', ∑ᶠ (w) (_ : w ∈ fibre W hΨ.choose y'), ∑ σ, t σ * sheetDensity W hΨ.choose (pot L) (χ σ) y' w =
        ∑ σ, t σ * ∑ᶠ (w) (_ : w ∈ fibre W hΨ.choose y'), sheetDensity W hΨ.choose (pot L) (χ σ) y' w :=
      fun y' => finsum_mem_sum (hfin y') t (fun σ w => sheetDensity W hΨ.choose (pot L) (χ σ) y' w)
    simp_rw [sheetDensity_sum W _ (pot L) t u χ hsum, hpt]
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl fun σ _ => MeasureTheory.integral_const_mul (t σ) _
    · intro σ _
      refine MeasureTheory.Integrable.const_mul ?_ (t σ)
      let A : HermLine ι :=
        { a := fun _ => 0
          h := fun z => Real.exp (-χ σ z)
          pos := fun z _ => Real.exp_pos _
          smul := fun c z hc => by simp [(hχ σ).inv c z hc] }
      have hAs : IsSmoothHerm A := Real.contDiff_exp.comp_contDiffOn (hχ σ).smooth.neg
      have hsec : IsSectionOn W A 1 :=
        ⟨fun _ => 0, fun k => by simp [A], isMultiHomog_one,
          fun h => hA.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)⟩
      have hlog : logNorm A 1 = χ σ := by
        funext z
        simp [logNorm, A, Real.exp_neg, Real.log_exp]
      have hI := hPI K ι W n hΨ.choose L A 1 hA hΨ.choose_spec hL hAs hsec
      rw [hlog] at hI
      exact hI
  · simp
end

