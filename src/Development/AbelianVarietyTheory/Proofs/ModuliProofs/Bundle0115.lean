module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TendstoOfSandwich
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsPowerGrowthVolumePullFiniteEndomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)

noncomputable section

namespace GlobalTheory.VolFin

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def regAlg [Algebra K X.functionField] (p : X ⟶ Sp K)
    (halg : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn p ⊤ a))
    (U : X.Opens) (h : genericPoint X ∈ U) : Subalgebra K X.functionField :=
  { (gen U h).rangeS with
    algebraMap_mem' := fun a => ⟨constFn p U a, (gen_constFn p U h a).trans (halg a).symm⟩ }

theorem mem_regAlg [Algebra K X.functionField] {p : X ⟶ Sp K} {halg} {U : X.Opens} {h}
    {f : X.functionField} : f ∈ regAlg p halg U h ↔ ∃ a, gen U h a = f := Iff.rfl

theorem sections_power_integral_iff_affine_cover [Algebra K X.functionField] (p : X ⟶ Sp K) (halg)
    {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (y : κ → X.functionField)
    (hy : ∀ i, tr N (c i) j₀ (hW i (hη i)) h₀ = y i) (e r : ℕ) :
    SectionsHaveFiniteDimension p (lbPow N e) r ↔ Module.Finite K (piece (fun i => regAlg p halg (W i) (hη i)) y e) ∧
      Module.finrank K (piece (fun i => regAlg p halg (W i) (hη i)) y e) = r := by
  refine lineBundle_global_sections_functionField_iff p halg (N := lbPow N e) (LB.isLB_linComb hN _ _) (fun _ => j₀)
    (Set.mem_iInter.2 fun _ => h₀) W (fun i _ => c i)
    (fun i _ hx => Set.mem_iInter.2 fun _ => hW i hx) hη hc _ (fun f => ?_) r
  refine forall_congr' fun i => ?_
  refine mem_regAlg.trans (exists_congr fun a => Eq.congr_right (congrArg (f * ·) ?_))
  exact ((tr_lbPow N e (fun _ => c i) (fun _ => j₀) _ _ (hW i (hη i)) h₀).trans
    (congrArg (· ^ e) (hy i))).symm

def constFF (p : X ⟶ Sp K) : K →+* X.functionField :=
  (gen ⊤ trivial).comp ((p.appLE ⊤ ⊤ (fun _ _ => trivial)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem den_of_section [Algebra K Y.functionField] (p : Y ⟶ Sp K) (halg) (M : LB Y) (j₀ : M.ι) (h₀)
    {κ : Type} [Finite κ] (W : κ → Y.Opens) (c : κ → M.ι) (hW : ∀ i, W i ≤ M.U (c i))
    (hη : ∀ i, genericPoint Y ∈ W i) (haff : ∀ i, IsAffineOpen (W i)) (d : ℕ) (s : (pw M d).Sec)
    (hs : IsAffineOpen (Out.nonzeroLocus s)) (hs' : genericPoint Y ∈ Out.nonzeroLocus s) :
    Den (fun i => regAlg p halg (W i) (hη i)) (fun i => tr M (c i) j₀ (hW i (hη i)) h₀) := by
  let σ := gen _ h₀ (s.f j₀)
  have hσ : σ ≠ 0 := by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hs'
    have hk' : genericPoint Y ∈ M.U k := Y.basicOpen_le _ hk
    have h1 := (mem_basicOpen_iff hk' (s.f k)).1 hk
    exact right_ne_zero_of_mul ((gen_sec s k j₀ hk' h₀).symm.trans_ne h1)
  let u : ∀ i, Γ(Y, W i) := fun i => rs Y (hW i) (s.f (c i))
  have hu : ∀ i, gen _ (hη i) (u i) = tr M (c i) j₀ (hW i (hη i)) h₀ ^ d * σ := fun i =>
    (gen_rs _ _ _).trans ((gen_sec s (c i) j₀ (hW i (hη i)) h₀).trans
      (congrArg (· * σ) (tr_pw M d _ _ _ _)))
  have hu0 : ∀ i, gen _ (hη i) (u i) ≠ 0 := fun i => by
    rw [hu]
    exact mul_ne_zero (pow_ne_zero _ (tr_ne_zero _ _ _ _ _)) hσ
  have hD : ∀ i, Y.basicOpen (u i) ≤ Out.nonzeroLocus s := fun i =>
    (Y.basicOpen_res (s.f (c i)) (homOfLE (hW i)).op).le.trans
      (inf_le_right.trans (le_iSup (fun k => Y.basicOpen (s.f k)) (c i)))
  have ev : ∀ a : Γ(Y, Out.nonzeroLocus s), ∀ᶠ n : ℕ in Filter.atTop, gen _ hs' a * σ ^ n ∈
      piece (fun i => regAlg p halg (W i) (hη i)) (fun i => tr M (c i) j₀ (hW i (hη i)) h₀)
        (d * n) := by
    intro a
    simp only [mem_piece]
    refine Filter.eventually_all.2 fun i => ?_
    filter_upwards [eventually_mul_pow (haff i) (hη i) (u i) (hu0 i) (hD i) hs' a] with n hn
    obtain ⟨b, hb⟩ := hn
    refine ⟨b, hb.trans ?_⟩
    rw [hu]
    ring
  intro t
  obtain ⟨a, b, hb, hab⟩ := exists_frac hs hs' t
  obtain ⟨n, hna, hnb⟩ := ((ev a).and (ev b)).exists
  refine ⟨d * n, _, hnb, mul_ne_zero hb (pow_ne_zero _ hσ), ?_⟩
  rw [← hab] at hna
  convert hna using 1
  ring

omit [IsIntegral Y] in
theorem exists_affine_cover [CompactSpace Y] {M : LB Y} (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → Y.Opens) (c : κ → M.ι), (∀ i, W i ≤ M.U (c i)) ∧
      (∀ i, ∃ x, x ∈ W i) ∧ (∀ i, IsAffineOpen (W i)) ∧ ∀ x, ∃ i, x ∈ W i := by
  have h : ∀ y : Y, ∃ (j : M.ι) (W : Y.Opens), IsAffineOpen W ∧ y ∈ W ∧ W ≤ M.U j := by
    intro y
    have hy : y ∈ ⨆ i, M.U i := hM.cover ▸ trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨W, hW, h1, h2⟩ := exists_isAffineOpen_mem_and_subset hj
    exact ⟨j, W, hW, h1, h2⟩
  choose c W h1 h2 h3 using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set Y))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, h2 y⟩)
  refine ⟨t, inferInstance, fun y => W y, fun y => c y, fun y => h3 y, fun y => ⟨y, h2 y⟩,
    fun y => h1 y, fun x => ?_⟩
  obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨⟨y, hy⟩, hx⟩

theorem vol_pull [CompactSpace Y] (p : Y ⟶ Sp K) (ψ : X ⟶ Y) [IsFinite ψ]
    (hψ : ψ (genericPoint X) = genericPoint Y) {D : ℕ} (hD : MapDeg ψ D) {M : LB Y} (hM : M.IsLB)
    (d : ℕ) (s : (pw M d).Sec) (hs : IsAffineOpen (Out.nonzeroLocus s))
    (hs' : genericPoint Y ∈ Out.nonzeroLocus s) {g : ℕ} {δ : ℝ} (hv : Vol p M g δ) :
    Vol (ψ ≫ p) (M.pull ψ) g (D * δ) := by
  obtain ⟨κ, _, W, c, hW, hne, haff, hc⟩ := exists_affine_cover hM
  have hη : ∀ i, genericPoint Y ∈ W i := fun i => generic_mem (hne i).choose_spec
  have hη' : ∀ i, genericPoint X ∈ ψ ⁻¹ᵁ W i := fun i => show ψ _ ∈ W i from hψ ▸ hη i
  obtain ⟨i₀, -⟩ := hc (genericPoint Y)
  letI : Algebra K Y.functionField := (constFF p).toAlgebra
  letI : Algebra K X.functionField := (constFF (ψ ≫ p)).toAlgebra
  letI : Algebra Y.functionField X.functionField := (ffMap ψ hψ).toAlgebra
  have halg : ∀ a, algebraMap K Y.functionField a = gen ⊤ trivial (constFn p ⊤ a) := fun _ => rfl
  have halg' : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn (ψ ≫ p) ⊤ a) :=
    fun _ => rfl
  have hφ : ∀ a, algebraMap Y.functionField X.functionField a = ffMap ψ hψ a := fun _ => rfl
  haveI : IsScalarTower K Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [hφ, halg, halg', ffMap_gen ψ hψ ⊤ trivial trivial]
    congr 1
    unfold constFn
    rw [Scheme.Hom.app_eq_appLE]
    exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE ψ p ⊤ ⊤ ⊤ (fun _ _ => trivial) (fun _ _ => trivial))).symm
  let R := fun i => regAlg p halg (W i) (hη i)
  let R' := fun i => regAlg (ψ ≫ p) halg' (ψ ⁻¹ᵁ W i) (hη' i)
  let y := fun i => tr M (c i) (c i₀) (hW i (hη i)) (hW i₀ (hη i₀))
  have hden : Den R y := den_of_section p halg M (c i₀) _ W c hW hη haff d s hs hs'
  have H : ∀ e r, SectionsHaveFiniteDimension p (lbPow M e) r ↔
      Module.Finite K (piece R y e) ∧ Module.finrank K (piece R y e) = r :=
    sections_power_integral_iff_affine_cover p halg hM (c i₀) (hW i₀ (hη i₀)) W c hW hη hc y fun _ => rfl
  have hW' : ∀ i, ψ ⁻¹ᵁ W i ≤ (M.pull ψ).U (fun _ => c i) := fun i =>
    le_trans (fun _ hx => hW i hx) (AbLaw.le_pull M ψ (le_refl (M.U (c i))))
  have H' : ∀ e r, SectionsHaveFiniteDimension (ψ ≫ p) (lbPow (M.pull ψ) e) r ↔
      Module.Finite K (piece R' (fun i => algebraMap _ X.functionField (y i)) e) ∧
        Module.finrank K (piece R' (fun i => algebraMap _ X.functionField (y i)) e) = r :=
    sections_power_integral_iff_affine_cover (ψ ≫ p) halg' (N := M.pull ψ) (LB.isLB_linComb hM _ _) (fun _ => c i₀)
      (hW' i₀ (hη' i₀)) (fun i => ψ ⁻¹ᵁ W i) (fun i _ => c i) hW' hη' (fun x => hc (ψ x)) _
      fun i => tr_pull M ψ hψ _ _ _ _ (hW i (hη i)) (hW i₀ (hη i₀))
  have hR : ∀ i, ∀ a ∈ R i, algebraMap _ X.functionField a ∈ R' i := by
    rintro i _ ⟨a, rfl⟩
    exact ⟨_, (ffMap_gen ψ hψ _ _ _ a).symm⟩
  have hS : ∀ i, ∀ t : X.functionField, ∃ a ∈ R' i, ∃ b ∈ R' i, b ≠ 0 ∧ t * b = a := by
    intro i t
    obtain ⟨a, b, hb, hab⟩ := exists_frac ((haff i).preimage ψ) (hη' i) t
    exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hb, hab⟩
  have hG : ∀ i, ∃ (n : ℕ) (v : Fin n → X.functionField), ∀ t ∈ R' i,
      ∃ w : Fin n → Y.functionField, (∀ l, w l ∈ R i) ∧ t = ∑ l, w l • v l := by
    intro i
    letI := (ψ.app (W i)).hom.toAlgebra
    haveI : Module.Finite Γ(Y, W i) Γ(X, ψ ⁻¹ᵁ W i) := IsFinite.finite_app ψ (W i) (haff i)
    obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Γ(Y, W i)) (M := Γ(X, ψ ⁻¹ᵁ W i))
    refine ⟨n, fun l => gen _ (hη' i) (v l), ?_⟩
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hv ▸ Submodule.mem_top : t ∈ Submodule.span Γ(Y, W i) (Set.range v))
    refine ⟨fun l => gen _ (hη i) (w l), fun l => ⟨_, rfl⟩, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, ffMap_gen ψ hψ _ _ (hη' i)]
    rfl
  haveI : Module.Finite Y.functionField X.functionField := by
    obtain ⟨n, v, hv⟩ := hG i₀
    exact finite_of_frac (R' i₀) (hS i₀) v fun t ht => (hv t ht).imp fun _ h => h.2
  have hrank : Module.finrank Y.functionField X.functionField = D := by
    haveI : Nonempty (W i₀) := ⟨⟨_, hη i₀⟩⟩
    haveI : Nonempty (ψ ⁻¹ᵁ W i₀) := ⟨⟨_, hη' i₀⟩⟩
    haveI := functionField_isFractionRing_of_isAffineOpen Y _ (haff i₀)
    haveI := functionField_isFractionRing_of_isAffineOpen X _ ((haff i₀).preimage ψ)
    letI := (ψ.app (W i₀)).hom.toAlgebra
    letI : Algebra Γ(Y, W i₀) X.functionField :=
      ((gen _ (hη' i₀)).comp (ψ.app (W i₀)).hom).toAlgebra
    haveI : IsScalarTower Γ(Y, W i₀) Γ(X, ψ ⁻¹ᵁ W i₀) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower Γ(Y, W i₀) Y.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun a => (ffMap_gen ψ hψ _ (hη i₀) (hη' i₀) a).symm
    rw [IsFractionRing.finrank_eq Γ(Y, W i₀) Y.functionField Γ(X, ψ ⁻¹ᵁ W i₀) X.functionField]
    exact Module.finrank_eq_of_rank_eq (hD _ (haff i₀) ⟨_, hη i₀⟩)
  obtain ⟨h, hh, hlim⟩ := hv
  have hfin := fun e => ((H e _).1 (hh e)).1
  have hrk := fun e => ((H e _).1 (hh e)).2
  obtain ⟨c₁, hup⟩ := upper (R' := R') hden hG hfin
  obtain ⟨c₂, hlo⟩ := lower hden hR hS fun e => (hup e).1
  refine ⟨_, fun e => (H' e _).2 ⟨(hup e).1, rfl⟩,
    tendsto_of_sandwich h _ D g c₂ c₁ δ hlim (fun e => ?_) fun e => ?_⟩
  · rw [← hrk, ← hrank]
    exact hlo e (hfin e)
  · rw [← hrk, ← hrank]
    exact (hup e).2

end GlobalTheory.VolFin

namespace GlobalTheory

theorem vol_pull_of_isFinite : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A) (D : ℕ) (M : LB P.A.left) (δ : ℝ), IsMonHom α → IsFinite α.left → MapDeg α.left D → M.IsLB → Out.RelAmple P.A M → Vol P.A.hom M P.g δ → Vol P.A.hom (M.pull α.left) P.g (D * δ) := by
  intro K _ _ P α D M δ hα hfin hD hM hamp hv
  haveI := polAV_isIntegral_of_isAlgClosed K P
  haveI := P.isAb.proper
  haveI : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have hsurj := (flat_and_surjective_of_isFinite_grpEnd K P.A α).2
  have hψ : α.left (genericPoint P.A.left) = genericPoint P.A.left := by
    have := (genericPoint_spec P.A.left).image α.left.continuous
    rw [Set.image_univ, α.left.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨d, -, n, s, hcov, hs⟩ := (Unif.relAmple_iff_veryAmpleBy K P.A M hM).1 hamp
  have hx : genericPoint P.A.left ∈ ⨆ i, Out.nonzeroLocus (s i) := hcov ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have := VolFin.vol_pull P.A.hom α.left hψ hD hM d (s i) (hs i).1 hi hv
  rwa [Over.w α] at this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppOfPullbackSnd
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.RigidLocal

open GlobalTheory.CechPic

private theorem surjective_app_of_eq_of_surjective_comp_injective {X S : Scheme.{0}} (f : X ⟶ S) {W V : S.Opens} (e : W = V)
    {R : CommRingCat} (g : Γ(X, f ⁻¹ᵁ W) ⟶ R)
    (h : Function.Surjective (f.app W ≫ g).hom) (hg : Function.Injective g.hom) :
    Function.Surjective (f.app V).hom := by
  subst e
  rw [CommRingCat.hom_comp, RingHom.coe_comp] at h
  exact h.of_comp_left hg

theorem surjective_app_of_pullback_snd {X S : Scheme.{0}} (f : X ⟶ S) (V : S.Opens)
    (h : Function.Surjective (pullback.snd f V.ι).appTop.hom) : Function.Surjective (f.app V).hom := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.coe_comp] at h
  have hi : IsIso (pullbackRestrictIsoRestrict f V).hom.appTop :=
    inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f V).hom.app ⊤))
  have h2 : Function.Surjective (f ∣_ V).appTop.hom :=
    h.of_comp_left (ConcreteCategory.bijective_of_isIso (pullbackRestrictIsoRestrict f V).hom.appTop).1
  rw [morphismRestrict_appTop] at h2
  refine surjective_app_of_eq_of_surjective_comp_injective f V.ι_image_top _ h2 ?_
  exact (ConcreteCategory.bijective_of_isIso
    (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f V ⊤)).op).hom).1

theorem eSec_comp {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] {φ : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (𝟙 S) φ) : eSec A ≫ φ = eSec A' :=
  (GlobalTheory.PolBaseChange.eSec_comm h).trans (Category.id_comp _)

theorem lbIso_of_local : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (φ : A.left ⟶ A'.left), IsAbelianScheme A → L.IsLB → L'.IsLB → Out.Rigidified A L → Out.Rigidified A' L' → IsGrpPullback A A' (𝟙 S) φ → (∀ p : S, ∃ (V B : Scheme.{0}) (x : V ⟶ S) (q : B ⟶ V) (a : B ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsPullback a q A.hom x ∧ LBIso (L.pull a) (L'.pull (a ≫ φ))) → LBIso L (L'.pull φ) := by
  intro hG S A A' _ _ L L' φ hA hL hL' hR hR' hφ hloc
  have hM : (L'.pull φ).IsLB := LB.isLB_pull hL' φ
  have hN : (LB.div L (L'.pull φ)).IsLB := LB.isLB_div hL hM

  have key : ∀ {Y : Scheme.{0}} (g : Y ⟶ A.left),
      (∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull g), t.IsGen) ↔
        GlobalTheory.CechPic.pull g (GlobalTheory.CechPic.cls L hL) = GlobalTheory.CechPic.pull g (GlobalTheory.CechPic.cls _ hM) := by
    intro Y g
    rw [← cls_eq_zero_iff (LB.isLB_pull hN g), cls_pull hN g (LB.isLB_pull hN g), cls_div hL hM hN,
      map_sub, sub_eq_zero]

  have hsec : ∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull (eSec A)), t.IsGen := by
    rw [key]
    have h1 : GlobalTheory.CechPic.pull (eSec A) (GlobalTheory.CechPic.cls L hL) = 0 := by
      rw [← cls_pull hL (eSec A) (LB.isLB_pull hL _)]
      exact (cls_eq_zero_iff _).2 hR
    have h2 : GlobalTheory.CechPic.pull (eSec A') (GlobalTheory.CechPic.cls L' hL') = 0 := by
      rw [← cls_pull hL' (eSec A') (LB.isLB_pull hL' _)]
      exact (cls_eq_zero_iff _).2 hR'
    rw [h1, cls_pull hL' φ hM, ← pull_comp, eSec_comp hφ, h2]

  have hloc' : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull (A.hom ⁻¹ᵁ U).ι), t.IsGen := by
    intro s
    obtain ⟨V, B, x, q, a, hx, hs, hpb, hiso⟩ := hloc s
    refine ⟨x.opensRange, hs, ?_⟩
    rw [key]
    have w : (A.hom ⁻¹ᵁ x.opensRange).ι ≫ A.hom = ((A.hom ∣_ x.opensRange) ≫ x.isoOpensRange.inv) ≫ x := by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
    obtain ⟨e, he⟩ : ∃ e, e ≫ a = (A.hom ⁻¹ᵁ x.opensRange).ι := ⟨hpb.lift _ _ w, hpb.lift_fst _ _ w⟩
    have ha : GlobalTheory.CechPic.pull a (GlobalTheory.CechPic.cls L hL) = GlobalTheory.CechPic.pull a (GlobalTheory.CechPic.cls _ hM) := by
      have h := (cls_eq_iff (LB.isLB_pull hL a) (LB.isLB_pull hL' (a ≫ φ))).2 hiso
      rw [cls_pull hL a, cls_pull hL' (a ≫ φ), pull_comp] at h
      rw [h, cls_pull hL' φ hM]
    rw [← he, pull_comp, pull_comp, ha]
  have hσ : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    exact (Over.w _).trans rfl
  have hsurj : ∀ U : S.Opens, Function.Surjective (A.hom.app U).hom := fun U =>
    surjective_app_of_pullback_snd A.hom U (surj_snd hG hA (Over.mk U.ι))
  obtain ⟨t, ht⟩ := exists_gen_of_local_of_section A.left S A.hom (eSec A) _ hN hσ hsurj hloc' hsec
  exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 ((cls_div hL hM hN).symm.trans ((cls_eq_zero_iff hN).2 ⟨t, ht⟩)))

end GlobalTheory.RigidLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TmapOfGlies
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem tmap_of_glies : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S S₁ S₂ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g (N' ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (y : S₂ ⟶ S₁) (s₂ : S₂ ⟶ Sp o) (u : TObj g (N' ^ 2) J b s₂) (ψ : u.A.left ⟶ A.left), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → GLies A act Q (y ≫ c) u ψ → LBIso u.L (L.pull ψ) → (∀ i, (u.pt i).left ≫ ψ = y ≫ (t₁.pt i).left ≫ ψ₁) → TMap u t₁ y := by
  intro o _ g N' J b S S₁ S₂ A _ L act Q c s₁ t₁ ψ₁ y s₂ u ψ hL ⟨h₁, h₄, _⟩ h₂ ⟨k₁, k₄, _⟩ k₂ k₃
  have hp := h₁.1
  obtain ⟨F, hF, hw⟩ : ∃ F : u.A.left ⟶ t₁.A.left, F ≫ ψ₁ = ψ ∧ F ≫ t₁.A.hom = u.A.hom ≫ y :=
    ⟨hp.lift ψ (u.A.hom ≫ y) (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  subst hF
  refine ⟨F, h₁.cancel k₁ hw, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans u.isLB (pull_isLB hL _) (pull_isLB t₁.isLB _) k₂ (lbIso_pull_comp h₂ F).symm
  · apply hp.hom_ext
    · rw [Category.assoc, k₃, Category.assoc]
    · have a₁ : (u.pt i).left ≫ u.A.hom = 𝟙 S₂ := Over.w (u.pt i)
      have a₂ : (t₁.pt i).left ≫ t₁.A.hom = 𝟙 S₁ := Over.w (t₁.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

end GlobalTheory.ZM.NearBuild
end
end

