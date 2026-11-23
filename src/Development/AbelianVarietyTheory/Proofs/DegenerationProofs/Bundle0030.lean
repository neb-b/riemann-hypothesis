module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EtaleMulNAndIsOpenOmOfIsSemiAbelian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem etale_mulN_and_isOpen_om (C : Core) (L : C.Law) (T : C.Theta) :
    letI := L.grp; Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left ∧ IsOpen (T.Om L) := by
  letI := L.grp
  letI := L.comm
  have := L.smooth
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have h : Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left := GlobalTheory.GrpTangent.etale_mulN C.GG T.m_unit
  exact ⟨h, (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left.isOpenMap _ (Out.nonzeroLocus T.s).isOpen⟩

theorem etale_mulN_and_isOpen_om_of_isSemiAbelian : ∀ (C : Core) (L : C.Law) (T : C.Theta), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → Out.MulNSt → Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left ∧ IsOpen (T.Om L) :=
  fun C L T _ _ => etale_mulN_and_isOpen_om C L T

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoverModelIrreducibleSpecialFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.IrrSplit

section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_lift (M : Model R A) (U : M.Y.left.Opens)
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) :
    IsPullback (IsOpenImmersion.lift U.ι (pullback.fst M.Y.hom (spMap (algebraMap R K))) hU)
      (pullback.snd M.Y.hom (spMap (algebraMap R K))) (U.ι ≫ M.Y.hom) (spMap (algebraMap R K)) := by
  refine ⟨⟨by rw [IsOpenImmersion.lift_fac_assoc, pullback.condition]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => pullback.lift (c.fst ≫ U.ι) c.snd (by simpa using c.condition)) ?_ ?_ ?_⟩⟩
  · intro c
    rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · intro c
    rw [pullback.lift_snd]
  · intro c m h₁ h₂
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← h₁, Category.assoc, IsOpenImmersion.lift_fac]
    · rw [pullback.lift_snd, h₂]

def restrictModel (M : Model R A) (U : M.Y.left.Opens) [QuasiCompact U.ι]
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) : Model R A where
  Y := Over.mk (U.ι ≫ M.Y.hom)
  e := Over.isoMk (g := (Over.pullback (spMap (algebraMap R K))).obj M.Y) (isPullback_lift M U hU).isoPullback.symm
    ((isPullback_lift M U hU).isoPullback_inv_snd) ≪≫ M.e
  smooth := by have := M.smooth; show Smooth (U.ι ≫ M.Y.hom); infer_instance
  sep := by have := M.sep; show IsSeparated (U.ι ≫ M.Y.hom); infer_instance
  qc := by have := M.qc; show QuasiCompact (U.ι ≫ M.Y.hom); infer_instance

theorem restrictModel_j (M : Model R A) (U : M.Y.left.Opens) [QuasiCompact U.ι]
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) :
    (restrictModel M U hU).j ≫ U.ι = M.j := by
  have h := (isPullback_lift M U hU).isoPullback_hom_fst
  show ((M.e.inv.left ≫ (isPullback_lift M U hU).isoPullback.hom) ≫
    pullback.fst (U.ι ≫ M.Y.hom) (spMap (algebraMap R K))) ≫ U.ι = _
  rw [Category.assoc, Category.assoc, reassoc_of% h, IsOpenImmersion.lift_fac]
  rfl

end

theorem exists_cover_irr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (M : Model R A), ∃ (n : ℕ) (N : Fin n → Model R A) (g : ∀ i, (N i).Y ⟶ M.Y), (∀ i, (N i).Irr ∧ IsOpenImmersion (g i).left ∧ (N i).j ≫ (g i).left = M.j) ∧ ∀ y ∈ M.sp, ∃ i, y ∈ Set.range (g i).left := by
  intro R K _ _ _ _ _ _ A M
  have := M.smooth
  have := M.qc
  let f : M.Y.left ⟶ Sp R := M.Y.hom
  let c : Sp R := IsLocalRing.closedPoint R
  have : IsLocallyNoetherian M.Y.left := LocallyOfFiniteType.isLocallyNoetherian f
  have hf : Smooth f := M.smooth
  have hf' : QuasiCompact f := M.qc
  have hs : Smooth (f.fiberToSpecResidueField c) :=
    inferInstanceAs (Smooth (pullback.snd f ((Sp R).fromSpecResidueField c)))
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
    ((Sp R).residueField c) (f.fiber c) (f.fiberToSpecResidueField c) hs
  have hn' : GlobalTheory.IsNormalScheme (f.fiber c) := GlobalTheory.IsNormalScheme.of_pred hn
  have : CompactSpace (f.fiber c) := inferInstance
  have : IsNoetherian (f.fiber c) := {}
  have hfin : (irreducibleComponents (f.fiber c)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hr : Set.range (f.fiberι c) = M.sp := f.range_fiberι c
  have hcl : Topology.IsClosedEmbedding (f.fiberι c) := by
    refine ⟨(f.fiberι c).isEmbedding, ?_⟩
    rw [f.range_fiberι]
    exact (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.continuous
  have : Finite (irreducibleComponents (f.fiber c)) := hfin
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin (irreducibleComponents (f.fiber c))
  let U : Fin n → M.Y.left.Opens := fun i => ⟨(f.fiberι c '' (σ.symm i).1ᶜ)ᶜ,
    (hcl.isClosedMap _ (GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (σ.symm i).2).isClosed_compl).isOpen_compl⟩
  have hU : ∀ i, Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range (U i).ι := by
    rintro i _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    rintro ⟨z, -, hz⟩
    have h1 : pullback.fst M.Y.hom (spMap (algebraMap R K)) x ∈ M.sp := hr ▸ ⟨z, hz⟩
    have h2 : M.Y.hom (pullback.fst M.Y.hom (spMap (algebraMap R K)) x) =
        spMap (algebraMap R K) (pullback.snd M.Y.hom (spMap (algebraMap R K)) x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h3 := h2.symm.trans h1
    generalize pullback.snd M.Y.hom (spMap (algebraMap R K)) x = p at h3
    have h4 : Ideal.comap (algebraMap R K) p.asIdeal = IsLocalRing.maximalIdeal R :=
      congrArg PrimeSpectrum.asIdeal h3
    have h5 : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top (K := K) p.asIdeal).resolve_right p.isPrime.ne_top
    rw [h5, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)] at h4
    exact IsDiscreteValuationRing.not_a_field R h4.symm
  have hmem : ∀ i z, f.fiberι c z ∈ U i ↔ z ∈ (σ.symm i).1 := by
    intro i z
    show f.fiberι c z ∉ f.fiberι c '' (σ.symm i).1ᶜ ↔ _
    rw [hcl.injective.mem_set_image]
    simp
  refine ⟨n, fun i => restrictModel M (U i) (hU i), fun i => Over.homMk (U i).ι rfl,
    fun i => ⟨?_, inferInstanceAs (IsOpenImmersion (U i).ι), restrictModel_j M (U i) (hU i)⟩, ?_⟩
  · have hi : IsIrreducible (f.fiberι c '' (σ.symm i).1) :=
      (σ.symm i).2.1.image _ (f.fiberι c).continuous.continuousOn
    have he : (restrictModel M (U i) (hU i)).sp = (U i).ι ⁻¹' (f.fiberι c '' (σ.symm i).1) := by
      ext y
      constructor
      · intro hy
        have : (U i).ι y ∈ M.sp := hy
        rw [← hr] at this
        obtain ⟨z, hz⟩ := this
        refine ⟨z, (hmem i z).1 ?_, hz⟩
        rw [hz]; exact y.2
      · rintro ⟨z, -, hz⟩
        have : (U i).ι y ∈ M.sp := hr ▸ ⟨z, hz⟩
        exact this
    show IsIrreducible _
    rw [he]
    refine ⟨?_, hi.2.preimage (U i).ι.isOpenEmbedding⟩
    obtain ⟨z, hz⟩ := (σ.symm i).2.1.1
    exact ⟨⟨_, (hmem i z).2 hz⟩, z, hz, rfl⟩
  · intro y hy
    rw [← hr] at hy
    obtain ⟨z, rfl⟩ := hy
    refine ⟨σ ⟨_, irreducibleComponent_mem_irreducibleComponents z⟩, ⟨_, (hmem _ z).2 ?_⟩, rfl⟩
    rw [Equiv.symm_apply_apply]
    exact mem_irreducibleComponent

end GlobalTheory.SS.IrrSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowSection
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecPow
variable {X X' : Scheme.{0}}

theorem add_pow_succ_of_mul_self {R : Type} [CommRing R] (t e : R) (he : e * e = 0) (m : ℕ) :
    (t + e) ^ (m + 1) = t ^ (m + 1) + ((m + 1 : ℕ) : R) * (t ^ m * e) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (t + e), ih]
    push_cast
    linear_combination ((m : R) + 1) * t ^ m * he

theorem eq_of_preimage_eq (β : X' ⟶ X) [Surjective β] {U V : X.Opens} (h : β ⁻¹ᵁ U = β ⁻¹ᵁ V) :
    U = V := by
  ext x
  obtain ⟨y, rfl⟩ := β.surjective x
  exact SetLike.ext_iff.1 h y

theorem app_rs (β : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (β.app V).hom (rs X h x) = rs X' (β.preimage_mono h) ((β.app U).hom x) := by
  have := GlobalTheory.LB.appLE_resG β h le_rfl x
  rw [Scheme.Hom.appLE_eq_app] at this
  exact this

theorem exists_lift_pow (β : X' ⟶ X) [IsClosedImmersion β] [Surjective β]
    (hsq : ∀ (W : X.Opens) (x y : Γ(X, W)), (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0)
    {V O : X.Opens} (hV : IsAffineOpen V) (hO : O ≤ V) (τ : Γ(X, O)) (s : Γ(X', β ⁻¹ᵁ V))
    (hs : X'.basicOpen s = β ⁻¹ᵁ O) (hτ : (β.app O).hom τ = rs X' (β.preimage_mono hO) s) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∃ σ : Γ(X, V), (β.app V).hom σ = s ^ k ∧ rs X hO σ = τ ^ k := by
  obtain ⟨t, rfl⟩ : ∃ t, (β.app V).hom t = s := β.app_surjective V hV s
  obtain rfl : X.basicOpen t = O :=
    eq_of_preimage_eq β ((Scheme.preimage_basicOpen β t).trans hs)
  have hε : (β.app _).hom (τ - rs X hO t) = 0 := by
    rw [map_sub, hτ, app_rs, sub_self]
  obtain ⟨n, w, hw⟩ : ∃ (n : ℕ) (w : Γ(X, V)), rs X hO w = rs X hO t ^ n * (τ - rs X hO t) :=
    exists_eq_pow_mul_of_isAffineOpen X V hV t (τ - rs X hO t)
  have h₁ : rs X' (β.preimage_mono hO) ((β.app V).hom w) = 0 := by
    rw [← app_rs β hO, hw, map_mul, hε, mul_zero]
  obtain ⟨l, hl⟩ : ∃ l : ℕ, (β.app V).hom t ^ l * (β.app V).hom w = 0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X' (hV.preimage β) _ _ ?_
    have := congrArg (rs X' hs.le) h₁
    rw [rs_rs, map_zero] at this
    exact this
  refine ⟨n + l + 1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = (n + l + j) + 1 := ⟨k - (n + l + 1), by omega⟩
  refine ⟨t ^ (n + l + j + 1) + ((n + l + j + 1 : ℕ) : Γ(X, V)) * (t ^ j * (t ^ l * w)), ?_, ?_⟩
  · simp only [map_add (f := _), map_mul, map_pow, hl, mul_zero, add_zero]
  · have e := add_pow_succ_of_mul_self (rs X hO t) (τ - rs X hO t) (hsq _ _ _ hε hε) (n + l + j)
    rw [add_sub_cancel] at e
    rw [e, map_add (f := _), map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_natCast, hw]
    ring

theorem exists_pow_eq {W O : X.Opens} (hW : IsCompact (W : Set X)) (hO : O ≤ W) (x y : Γ(X, W))
    (hsq : (y - x) * (y - x) = 0) (hx : X.basicOpen x ≤ O) (h : rs X hO x = rs X hO y) :
    ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → x ^ l = y ^ l := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, x ^ m * (y - x) = 0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hW _ _ ?_
    have := congrArg (rs X hx) h
    rw [rs_rs, rs_rs] at this
    change rs X (hx.trans hO) (y - x) = 0
    rw [map_sub, this, sub_self]
  refine ⟨m + 1, fun l hl => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, l = (j + m) + 1 := ⟨l - (m + 1), by omega⟩
  have e := add_pow_succ_of_mul_self x (y - x) hsq (j + m)
  rw [add_sub_cancel, pow_add x j m, _root_.mul_assoc, hm] at e
  simpa using e.symm

theorem exists_finite_affine_cover [CompactSpace X] {H : LB X} (hH : H.IsLB) :
    ∃ (I : Type) (_ : Finite I) (V : I → X.Opens) (c : I → H.ι),
      (∀ a, IsAffineOpen (V a)) ∧ (∀ a, V a ≤ H.U (c a)) ∧ ⊤ ≤ ⨆ a, V a := by
  have h : ∀ x : X, ∃ (V : X.Opens) (i : H.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ H.U i := fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (Set.mem_univ x))
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hi (H.U i).isOpen
    exact ⟨V, i, hV, hx, hle⟩
  choose V c hV hx hle using h
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨S, inferInstance, fun a => V a, fun a => c a, fun a => hV a, fun a => hle a, fun x _ => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem basicOpen_rs_eq {H : LB X} (s : LB.Sec H) (i : H.ι) {V : X.Opens} (h : V ≤ H.U i) :
    X.basicOpen (rs X h (s.f i)) = V ⊓ nonzeroLocus s := by
  apply le_antisymm
  · refine le_inf (X.basicOpen_le _) ?_
    erw [Scheme.basicOpen_res]
    exact inf_le_right.trans (le_iSup (fun k => X.basicOpen (s.f k)) i)
  · have hu := SecOn.isUnit_rs_of_le_nonzeroLocus s i (O := V ⊓ nonzeroLocus s)
      (inf_le_left.trans h) inf_le_right
    rw [← rs_rs h inf_le_left] at hu
    have e := X.basicOpen_of_isUnit hu
    erw [Scheme.basicOpen_res] at e
    exact e.ge.trans inf_le_right

theorem exists_pow_section : ∀ (X X' : Scheme.{0}) (β : X' ⟶ X) [IsClosedImmersion β] [Surjective β] [CompactSpace X] [QuasiSeparatedSpace X], (∀ (W : X.Opens) (x y : Γ(X, W)), (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0) → ∀ H : LB X, H.IsLB → ∀ (s₀ : LB.Sec (H.pull β)) (D : X.Opens), β ⁻¹ᵁ D = nonzeroLocus s₀ → ∀ t : SecOn H D, SecOn.pull H β D t = GlobalTheory.LB.ofSec s₀ (β ⁻¹ᵁ D) → ∃ n : ℕ, 1 ≤ n ∧ ∃ σ : LB.Sec (pw H n), nonzeroLocus σ = D := by
  intro X X' β _ _ _ _ hsq H hH s₀ D hD t ht
  obtain ⟨I, _, V, c, hV, hc, hcov⟩ := exists_finite_affine_cover hH
  let s (a : I) : Γ(X', β ⁻¹ᵁ V a) := rs X' (le_pull H β (hc a)) (s₀.f fun _ => c a)
  let τ (a : I) : Γ(X, V a ⊓ D) :=
    rs X (le_inf inf_le_right (inf_le_left.trans (hc a))) (GlobalTheory.LB.coord t (c a))
  have hs (a : I) : X'.basicOpen (s a) = β ⁻¹ᵁ (V a ⊓ D) :=
    (basicOpen_rs_eq s₀ (fun _ => c a) (le_pull H β (hc a))).trans
      (congrArg (β ⁻¹ᵁ V a ⊓ ·) hD.symm)
  have hτ (a : I) : (β.app _).hom (τ a) = rs X' (β.preimage_mono inf_le_left) (s a) := by
    have e := congrArg (fun z => rs X' (le_inf (β.preimage_mono inf_le_right)
      (le_pull H β (inf_le_left.trans (hc a))) :
        β ⁻¹ᵁ (V a ⊓ D) ≤ β ⁻¹ᵁ D ⊓ (H.pull β).U fun _ => c a) (GlobalTheory.LB.coord z fun _ => c a)) ht
    rw [app_rs, rs_rs]
    exact ((GlobalTheory.LB.resG_appLE β _ _ _).symm.trans e).trans (rs_rs _ _ _)
  choose k₀ hk₀ using fun a => exists_lift_pow β hsq (hV a) inf_le_left (τ a) (s a) (hs a) (hτ a)
  obtain ⟨k₁, hk₁⟩ := (Set.finite_range k₀).bddAbove
  choose σ hσs hστ using fun a => hk₀ a (k₁ + 1) ((hk₁ ⟨a, rfl⟩).trans (Nat.le_succ _))
  have hbo (a : I) : X.basicOpen (σ a) = V a ⊓ D := by
    refine eq_of_preimage_eq β ((Scheme.preimage_basicOpen β _).trans ?_)
    rw [← hs, ← X'.basicOpen_pow (s a) (Nat.succ_pos k₁)]
    exact congrArg X'.basicOpen (hσs a)
  let g (a b : I) : Γ(X, V a ⊓ V b) := rs X (inf_le_inf (hc a) (hc b)) (H.g (c a) (c b)).val
  have key (p : I × I) : ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → rs X inf_le_left (σ p.1) ^ l =
      (g p.1 p.2 ^ (k₁ + 1) * rs X inf_le_right (σ p.2)) ^ l := by
    obtain ⟨a, b⟩ := p
    have hsm : (β.app _).hom (g a b ^ (k₁ + 1) * rs X inf_le_right (σ b) -
        rs X inf_le_left (σ a)) = 0 := by
      have e := GlobalTheory.LB.sec_rel s₀ (fun _ => c a) (fun _ => c b) (W := β ⁻¹ᵁ (V a ⊓ V b))
        (le_pull H β (inf_le_left.trans (hc a))) (le_pull H β (inf_le_right.trans (hc b)))
        (le_inf (le_pull H β (inf_le_left.trans (hc a))) (le_pull H β (inf_le_right.trans (hc b))))
      erw [GlobalTheory.LB.resG_pull_g] at e
      rw [map_sub, map_mul, map_pow, app_rs, app_rs, app_rs, hσs, hσs, map_pow, map_pow, rs_rs, rs_rs,
        ← mul_pow, sub_eq_zero]
      exact congrArg (· ^ (k₁ + 1)) e.symm
    refine exists_pow_eq (O := V a ⊓ V b ⊓ D)
      (QuasiSeparatedSpace.inter_isCompact _ _ (V a).isOpen (hV a).isCompact (V b).isOpen
        (hV b).isCompact) inf_le_left _ _ (hsq _ _ _ hsm hsm) ?_ ?_
    · erw [Scheme.basicOpen_res]
      rw [hbo]
      exact inf_le_inf_left _ inf_le_right
    · have ea := congrArg (rs X (inf_le_inf_right D inf_le_left : V a ⊓ V b ⊓ D ≤ V a ⊓ D)) (hστ a)
      have eb := congrArg (rs X (inf_le_inf_right D inf_le_right : V a ⊓ V b ⊓ D ≤ V b ⊓ D)) (hστ b)
      rw [rs_rs, map_pow, rs_rs] at ea eb
      rw [map_mul, map_pow, rs_rs, rs_rs, rs_rs, ea, eb, ← mul_pow]
      exact congrArg (· ^ (k₁ + 1)) (SecOn.compat t (c a) (c b) _ _ _)
  choose l₀ hl₀ using key
  obtain ⟨l₁, hl₁⟩ := (Set.finite_range l₀).bddAbove
  obtain ⟨u, hu, -⟩ := SecOn.existsUnique_of_local (V := ⊤)
    (isLB_pw hH (((k₁ + 1) * (l₁ + 1) : ℕ) : ℤ)) V (fun _ => le_top) hcov c hc
    (fun a => σ a ^ (l₁ + 1)) fun a b => by
      have e := hl₀ (a, b) (l₁ + 1) ((hl₁ ⟨(a, b), rfl⟩).trans (Nat.le_succ _))
      rw [mul_pow, ← pow_mul] at e
      rw [map_pow, map_pow]
      refine e.trans (congrArg (· * _) ?_)
      change _ = rs X (inf_le_inf (hc a) (hc b)) (H.g (c a) (c b) ^ (((k₁ + 1) * (l₁ + 1) : ℕ) : ℤ)).val
      rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  refine ⟨(k₁ + 1) * (l₁ + 1), Nat.succ_le_of_lt (by positivity), SecOn.topEquiv _ u, ?_⟩
  have hloc (a : I) : V a ⊓ nonzeroLocus (SecOn.topEquiv _ u) = V a ⊓ D := by
    rw [← basicOpen_rs_eq (SecOn.topEquiv _ u) (c a) (hc a), ← hbo,
      ← X.basicOpen_pow (σ a) (Nat.succ_pos l₁)]
    exact congrArg X.basicOpen ((rs_rs _ _ _).trans (hu a))
  ext x
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov (Set.mem_univ x))
  have e := SetLike.ext_iff.1 (hloc a) x
  exact ⟨fun h => (e.1 ⟨ha, h⟩).2, fun h => (e.2 ⟨ha, h⟩).2⟩

end GlobalTheory.SecPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelOfProperBase
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_semiAbelian_model_of_proper_base :
    ∀ (o W L : Type) [CommRing o] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (β : o →+* W) (Z : Scheme.{0}) (s : Z ⟶ Sp o) (x : Sp L ⟶ Z) (G : Over Z) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper s → x ≫ s = spMap ((algebraMap W L).comp β) → IsSemiAbelian G → IsGrpPullback A G x φ → ∃ (G' : Over (Sp W)) (_ : GrpObj G') (e : (Over.pullback (spMap (algebraMap W L))).obj G' ≅ A), IsSemiAbelian G' ∧ IsMonHom e.hom := by
  intro o W L _ _ _ _ _ _ _ β Z s x G _ A _ φ hs hx hG hA
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  have hw : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap W L)) ≫ spMap β := by
    rw [hx, ← Spec.map_comp]; rfl
  obtain ⟨⟨y, hy, -⟩⟩ := (hE { R := W, K := L, i₁ := x, i₂ := spMap β, commSq := ⟨hw⟩ }).exists_lift
  have hy' : spMap (algebraMap W L) ≫ y = x := hy
  obtain ⟨e, he, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback ((Over.pullback y).obj G) (spMap (algebraMap W L))).comp
      (isGrpPullback_pullback G y)).congr hy' rfl) hA
  exact ⟨(Over.pullback y).obj G, inferInstance, e, IsSemiAbelian.pullback y G hG, he⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecMapFromSpecOfRangeSubset
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.extension_descends_of_isIntegral : ∀ (R R₂ : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (g : R →+* R₂) (gam : FractionRing R →+* FractionRing R₂), (∀ r, gam (algebraMap R _ r) = algebraMap R₂ _ (g r)) → g.IsIntegral → ∀ (X : Scheme.{0}) (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing R) ⟶ X) (χ₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R₂ ⟶ X), _root_.ReciprocityTheory.ChartRestriction.G.Out.jK R₂ ≫ χ₂ = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap gam ≫ y → ∃ χ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ X, _root_.ReciprocityTheory.ChartRestriction.G.Out.jK R ≫ χ = y ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap g ≫ χ = χ₂ := by
  intro R R₂ _ _ _ _ _ _ g gam hgam hint X y χ₂ hcomm
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap _root_.ReciprocityTheory.ChartRestriction.G.Out.jK at *
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := χ₂ (IsLocalRing.closedPoint R₂)) (U := ⊤) trivial
  have hmem : ∀ p, χ₂ p ∈ U := fun p =>
    ((IsLocalRing.specializes_closedPoint (R := R₂) p).map χ₂.continuous).mem_open U.2 hxU
  have h₂ : Set.range χ₂ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact hmem p
  have hy : Set.range y ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    let q : ↥(Spec (CommRingCat.of (FractionRing R₂))) :=
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
    have hp : (Spec.map (CommRingCat.ofHom gam)) q = p := Subsingleton.elim _ _
    have e := Scheme.Hom.comp_apply
      (Spec.map (CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂)))) χ₂ q
    rw [hcomm, Scheme.Hom.comp_apply, hp] at e
    rw [e]
    exact hmem _
  set χ₂' := IsOpenImmersion.lift U.ι χ₂ h₂ with hχ₂'
  set y' := IsOpenImmersion.lift U.ι y hy with hy'
  have hc' : Spec.map (CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂))) ≫ χ₂' =
      Spec.map (CommRingCat.ofHom gam) ≫ y' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hχ₂', hy', IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, hcomm]
  set a₂ := Spec.preimage (χ₂' ≫ hU.isoSpec.hom) with ha₂
  set b := Spec.preimage (y' ≫ hU.isoSpec.hom) with hb
  have hab : a₂ ≫ CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂)) =
      b ≫ CommRingCat.ofHom gam := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ha₂, hb, Spec.map_preimage, Spec.map_preimage,
      ← Category.assoc, ← Category.assoc, hc']
  have e1 : ∀ a, gam (b.hom a) = algebraMap R₂ _ (a₂.hom a) := fun a =>
    (congrArg (fun f => f.hom a) hab).symm
  have hcomp : gam.comp (algebraMap R (FractionRing R)) =
      (algebraMap R₂ (FractionRing R₂)).comp g :=
    RingHom.ext hgam
  have hpt : ∀ a, b.hom a ∈ (algebraMap R (FractionRing R)).range := by
    intro a
    obtain ⟨p, hpm, hp⟩ := hint (a₂.hom a)
    rw [RingHom.mem_range]
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    refine ⟨p, hpm, gam.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, e1, hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  let e := RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
    ⟨fun u v h => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  let φ : Γ(X, U) →+* R := e.symm.toRingHom.comp (b.hom.codRestrict _ hpt)
  have hφ : ∀ a, algebraMap R (FractionRing R) (φ a) = b.hom a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨b.hom a, hpt a⟩)
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv ≫ U.ι, ?_, ?_⟩
  · have hφb : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = b := by
      ext a
      exact hφ a
    rw [← Category.assoc, ← Spec.map_comp, hφb, hb, Spec.map_preimage, Category.assoc,
      Iso.hom_inv_id_assoc, hy', IsOpenImmersion.lift_fac]
  · have hφa : CommRingCat.ofHom φ ≫ CommRingCat.ofHom g = a₂ := by
      ext a
      apply IsFractionRing.injective R₂ (FractionRing R₂)
      change algebraMap R₂ _ (g (φ a)) = algebraMap R₂ _ (a₂.hom a)
      rw [← hgam, hφ, e1]
    rw [← Category.assoc, ← Spec.map_comp, hφa, ha₂, Spec.map_preimage, Category.assoc,
      Iso.hom_inv_id_assoc, hχ₂', IsOpenImmersion.lift_fac]

end GlobalTheory
end

