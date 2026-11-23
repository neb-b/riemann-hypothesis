module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBPullIsoOfIsOpenImmersion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem bijective_appLE_of_le_opensRange {Y Y' : Scheme.{0}} (e : Y' ⟶ Y) [IsOpenImmersion e]
    {V : Y.Opens} (hV : V ≤ e.opensRange) {V' : Y'.Opens} (h : V' ≤ e ⁻¹ᵁ V) (h' : e ⁻¹ᵁ V ≤ V') :
    Function.Bijective (e.appLE V V' h).hom := by
  obtain rfl : V' = e ⁻¹ᵁ V := le_antisymm h h'
  have := e.isIso_app V hV
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (e.app V)

theorem SecOn.pullLE_bijective_of_le_opensRange {Y Y' : Scheme.{0}} (M : LB Y) (e : Y' ⟶ Y)
    [IsOpenImmersion e] {V : Y.Opens} (hV : V ≤ e.opensRange) {V' : Y'.Opens}
    (h : V' ≤ e ⁻¹ᵁ V) (h' : e ⁻¹ᵁ V ≤ V') :
    Function.Bijective (SecOn.pullLE M e V V' h) := by
  have hb (i : M.ι) : Function.Bijective (e.appLE (V ⊓ M.U i) (V' ⊓ (M.pull e).U fun _ => i)
      ((inf_le_inf_right _ h).trans (GlobalTheory.LB.pull_inf_le e V fun _ => i))).hom :=
    bijective_appLE_of_le_opensRange e (inf_le_left.trans hV) _
      (inf_le_inf h' (GlobalTheory.LB.pull_U (L := M) e fun _ => i).ge)
  refine ⟨fun s t hst => GlobalTheory.LB.sec_ext fun i => (hb i).1 ?_, fun t => ?_⟩
  · exact (SecOn.coord_pullLE e h s fun _ => i).symm.trans
      ((congrArg (GlobalTheory.LB.coord · fun _ => i) hst).trans (SecOn.coord_pullLE e h t fun _ => i))
  · choose a ha using fun i => (hb i).2 (GlobalTheory.LB.coord t fun _ => i)
    refine ⟨GlobalTheory.LB.mkSec a fun i j => ?_, GlobalTheory.LB.sec_ext fun j =>
      (SecOn.coord_pullLE e h _ j).trans (ha (j PUnit.unit))⟩
    have e₁ : V' ⊓ (M.pull e).U (fun _ => i) ⊓ (M.pull e).U (fun _ => j) ≤
        e ⁻¹ᵁ (V ⊓ M.U i ⊓ M.U j) :=
      inf_le_inf ((inf_le_inf_right _ h).trans (GlobalTheory.LB.pull_inf_le e V fun _ => i))
        (GlobalTheory.LB.pull_U_le (L := M) e fun _ => j)
    refine (bijective_appLE_of_le_opensRange e (inf_le_left.trans (inf_le_left.trans hV)) e₁
      (inf_le_inf (inf_le_inf h' (GlobalTheory.LB.pull_U (L := M) e fun _ => i).ge)
        (GlobalTheory.LB.pull_U (L := M) e fun _ => j).ge)).1 ?_
    have := GlobalTheory.LB.coord_mem t (fun _ => i) (fun _ => j)
    rw [← ha i, ← ha j, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE] at this
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG]
    exact this.trans (congrArg (· * _) (GlobalTheory.LB.resG_pull_g (L := M) e (fun _ => i) (fun _ => j) _))

theorem cechLB_pull_iso_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (Y' : Scheme.{0}) (e : Y' ⟶ Y) [IsOpenImmersion e] (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), M.IsLB → (∀ i, D i ≤ e.opensRange) → Nonempty (cechLB (e ≫ f) (M.pull e) (fun i => e ⁻¹ᵁ D i) ≅ cechLB f M D) := by
  intro R _ Y f M Y' e _ κ _ _ D _ hD
  have w : e ≫ f = (e ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  let φ : secCube f M D ⟶ secCube (e ≫ f) (M.pull e) fun i => e ⁻¹ᵁ D i :=
    GlobalTheory.Cube.homMk κ R (fun s => secCubePull M D w s) fun h x => secCubePull_res D w h x
  have : IsIso (cechComplexMap φ) := isIso_cechComplexMap φ fun s ⟨i, hi⟩ =>
    SecOn.pullLE_bijective_of_le_opensRange M e ((biInf_le D hi).trans (hD i))
      (preimage_biInf D e s).ge (preimage_biInf D e s).le
  exact ⟨(asIso (cechComplexMap φ)).symm⟩

end GlobalTheory.AbLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CstSmoothAndFlat
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.Cohom

theorem cst_smooth_and_flat : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (V : Y.Opens), IsAffineOpen V → (Smooth f → (cst f V).Smooth) ∧ (Flat f → (cst f V).Flat) := by
  intro R _ Y f V hV
  have e : cst f V = (f.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := rfl
  have hb : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  rw [e]
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · exact (RingHom.Smooth.of_bijective hb).comp (f.smooth_appLE (isAffineOpen_top _) hV le_top)
  · exact (RingHom.Flat.of_bijective hb).comp (f.flat_appLE (isAffineOpen_top _) hV le_top)

end GlobalTheory.Cohom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
section
open CategoryTheory DirectSum MvPolynomial

noncomputable section

namespace GlobalTheory

open GradedHilbert

section

variable {ι : Type} {R : Type} [CommRing R]

theorem GrSum.X_smul_bijective {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x) {i : ι}
    (h : ∀ t, Function.Bijective (x i t)) :
    Function.Bijective fun m : GrSum hx => (X i : MvPolynomial ι R) • m := by
  have hg := isGradedMap_lsmul (GrSum.grading hx) (X_mem_polyGrading (R := R) i)
  refine ⟨hg.injective_iff.2 fun n => ?_, hg.surjective_iff.2 fun n => ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ e
    have e' : (X i : MvPolynomial ι R) • GrSum.of hx n a = (X i : MvPolynomial ι R) • GrSum.of hx n b :=
      congrArg Subtype.val e
    rw [GrSum.X_smul_of, GrSum.X_smul_of] at e'
    obtain rfl := (h n).1 (GrSum.of_injective hx _ e')
    rfl
  · rintro ⟨_, b, rfl⟩
    obtain ⟨a, rfl⟩ := (h n).2 b
    exact ⟨⟨_, a, rfl⟩, Subtype.ext (GrSum.X_smul_of hx i n a)⟩

theorem xProd_smul_bijective_of {N : Type} [AddCommGroup N] [Module (MvPolynomial ι R) N]
    (s : Finset ι) (h : ∀ i ∈ s, Function.Bijective fun m : N => (X i : MvPolynomial ι R) • m) :
    Function.Bijective fun m : N => xProd R s • m := by
  refine Finset.prod_induction _ (fun p : MvPolynomial ι R => Function.Bijective fun m : N => p • m)
    (fun p q hp hq => ?_) ?_ h
  · simp only [mul_smul]
    exact hp.comp hq
  · simp only [one_smul]
    exact Function.bijective_id

theorem exists_homLoc_bijective_of
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] [Decomposition ℳ]
    {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩] [Decomposition 𝒩]
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι)
    (hb : Function.Bijective fun m : N => xProd R s • m)
    (h₁ : ∀ n, ∀ y ∈ ℳ n, f y = 0 → ∃ k : ℕ, xProd R s ^ k • y = 0)
    (h₂ : ∀ n, ∀ a ∈ 𝒩 n, ∃ (k : ℕ) (y : M), f y = xProd R s ^ k • a) (n : ℤ) :
    ∃ φ : homLoc ℳ s n →ₗ[R] 𝒩 n, Function.Bijective φ ∧
      ∀ (z : homLoc ℳ s n) (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
        xProd R s ^ k • (φ z : N) = f m := by
  let e := LinearEquiv.ofBijective _ (toHomLoc_bijective 𝒩 hb n)
  refine ⟨e.symm.toLinearMap ∘ₗ homLocMap hf s n, e.symm.bijective.comp ⟨?_, ?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, k, m, hm, rfl⟩ hz
    have hz' : awayMap _ f (awayFrac M (xProd R s) k m) = 0 := congrArg Subtype.val hz
    rw [awayMap_awayFrac, map_eq_zero_iff _ (awayFrac_injective hb.1 k)] at hz'
    exact Subtype.ext (awayFrac_eq_zero_iff.2 (h₁ _ m hm hz'))
  · refine homLocMap_surjective_of hf (fun y => ?_) n
    induction y using Decomposition.inductionOn 𝒩 with
    | zero => exact ⟨0, by simp⟩
    | @homogeneous d a =>
      obtain ⟨k, y, hy⟩ := h₂ d a a.2
      exact ⟨k, y, hy⟩
    | add a b ha hb =>
      obtain ⟨k, ha⟩ := ha
      obtain ⟨j, hb⟩ := hb
      refine ⟨k + j, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [add_comm, pow_add, mul_smul]
        exact Submodule.smul_mem _ _ ha
      · rw [pow_add, mul_smul]
        exact Submodule.smul_mem _ _ hb
  · intro z k m hm
    have h : awayFrac N (xProd R s) 0 (e.symm (homLocMap hf s n z) : N) = awayMap _ f z :=
      congrArg Subtype.val (e.apply_symm_apply (homLocMap hf s n z))
    apply awayFrac_injective hb.1 0
    rw [map_smul]
    erw [h]
    rw [← hm, awayMap_awayFrac, pow_smul_awayFrac]

theorem exists_homLoc_bijective_grSum
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] [Decomposition ℳ]
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {f : M →ₗ[MvPolynomial ι R] GrSum hx} (hf : IsGradedMap ℳ (GrSum.grading hx) f) (s : Finset ι)
    (hb : ∀ i ∈ s, ∀ t, Function.Bijective (x i t))
    (h₁ : ∀ n, ∀ y ∈ ℳ n, f y = 0 → ∃ k : ℕ, xProd R s ^ k • y = 0)
    (h₂ : ∀ n (a : A n), ∃ (k : ℕ) (y : M), f y = xProd R s ^ k • GrSum.of hx n a) (n : ℤ) :
    ∃ φ : homLoc ℳ s n →ₗ[R] A n, Function.Bijective φ ∧
      ∀ (z : homLoc ℳ s n) (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
        xProd R s ^ k • GrSum.of hx n (φ z) = f m := by
  obtain ⟨ψ, hψ, hψ'⟩ := exists_homLoc_bijective_of hf s
    (xProd_smul_bijective_of s fun i hi => GrSum.X_smul_bijective hx (hb i hi)) h₁
    (by rintro n _ ⟨a, rfl⟩; exact h₂ n a) n
  refine ⟨(GrSum.pieceEquiv hx n).symm.toLinearMap ∘ₗ ψ,
    (GrSum.pieceEquiv hx n).symm.bijective.comp hψ, fun z k m e => ?_⟩
  rw [← hψ' z k m e]
  exact congrArg (fun w : GrSum.grading hx n => xProd R s ^ k • (w : GrSum hx))
    ((GrSum.pieceEquiv hx n).apply_symm_apply (ψ z))

theorem homLoc_grSum_res
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ]
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {B : ℤ → Type} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    {y : ι → ∀ n, B n →ₗ[R] B (n + 1)} (hy : OperatorsCommute y)
    (r : ∀ n, A n →ₗ[R] B n) (hr : ∀ i n a, r (n + 1) (x i n a) = y i n (r n a))
    {f : M →ₗ[MvPolynomial ι R] GrSum hx} (hf : IsGradedMap ℳ (GrSum.grading hx) f)
    {g : M →ₗ[MvPolynomial ι R] GrSum hy}
    (hfg : ∀ n m a, f m = GrSum.of hx n a → g m = GrSum.of hy n (r n a))
    {s t : Finset ι} (h : s ⊆ t) (hb : ∀ i ∈ t, ∀ n, Function.Bijective (y i n)) {n : ℤ}
    (z : homLoc ℳ s n) (a : A n) (b : B n)
    (ha : ∀ (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
      xProd R s ^ k • GrSum.of hx n a = f m)
    (hb' : ∀ (k : ℕ) (m : M), awayFrac M (xProd R t) k m = homLocRes ℳ h n z →
      xProd R t ^ k • GrSum.of hy n b = g m) : b = r n a := by
  obtain ⟨k, m, hm, e⟩ := z.2
  obtain ⟨a', ha'⟩ := hf hm
  have h1 : g m = GrSum.map hx hy r hr (f m) := by
    rw [hfg _ m a' ha'.symm, ← ha', GrSum.map_of]
  obtain ⟨c, hc⟩ : ∃ c, xProd R t = c * xProd R s :=
    exists_eq_mul_left_of_dvd (Finset.prod_dvd_prod_of_subset s t X h)
  have h2 := hb' k (c ^ k • m) (by rw [coe_homLocRes, ← e, locRes_awayFrac X h hc])
  rw [map_smul, h1, ← ha k m e, map_smul, GrSum.map_of, ← mul_smul, ← mul_pow, ← hc] at h2
  have h3 := xProd_smul_bijective_of t fun i hi => GrSum.X_smul_bijective hy (hb i hi)
  exact GrSum.of_injective hy n (IsSMulRegular.pow k h3.1 h2)

end

theorem exists_grCube_hom_bijective (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R]
    (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢] (A : ℤ → Cube.{0} ι R) (x : ι → ∀ t, A t ⟶ A (t + 1))
    (hx : ∀ I : Finset ι,
      OperatorsCommute (A := fun t => (A t).obj I) fun i t => ((x i t).app I).hom)
    (ρ : ∀ I : Finset ι, G →ₗ[MvPolynomial ι R] GrSum (hx I))
    (hρ : ∀ I, IsGradedMap 𝒢 (GrSum.grading (hx I)) (ρ I))
    (hres : ∀ (I J : Finset ι) (h : I ⊆ J) (n : ℤ) (y : G) (a : (A n).obj I),
      ρ I y = GrSum.of (hx I) n a → ρ J y = GrSum.of (hx J) n (Cube.res (A n) h a))
    (hbij : ∀ (I : Finset ι), ∀ i ∈ I, ∀ t, Function.Bijective ((x i t).app I).hom)
    (hker : ∀ (I : Finset ι) (n : ℤ), ∀ y ∈ 𝒢 n, ρ I y = 0 → ∃ k : ℕ, xProd R I ^ k • y = 0)
    (hcoker : ∀ (I : Finset ι) (t : ℤ) (a : (A t).obj I), ∃ (k : ℕ) (y : G),
      ρ I y = xProd R I ^ k • GrSum.of (hx I) t a) (t : ℤ) :
    ∃ φ : grCube ι 𝒢 t ⟶ A t, ∀ I, Function.Bijective (φ.app I).hom := by
  choose φ hφ hφ' using fun I =>
    exists_homLoc_bijective_grSum (hx I) (hρ I) I (hbij I) (hker I) (hcoker I) t
  refine ⟨Cube.homMk (ι := ι) (R := R) (A := grCube ι 𝒢 t) φ fun {I J} h z => ?_, hφ⟩
  exact homLoc_grSum_res (hx I) (hx J) (fun n => Cube.res (A n) h)
    (fun i n a => (Cube.app_res (x i n) h a).symm) (hρ I) (hres I J h) h (hbij J) z _ _
    (hφ' I z) (hφ' J _)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNhdsPowMulTwCoordEqZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_nhds_pow_mul_twCoord_eq_zero {Y : Scheme.{0}} {H M : LB Y} {d : ℤ}
    (σ : LB.Sec (pw H d)) {t : ℤ} (hH : H.IsLB) (hM : M.IsLB) (a : SecOn (tw M H t) ⊤)
    (ha : SecOn.restrict _ (le_top : nonzeroLocus σ ≤ ⊤) a = 0) (x : Y) :
    ∃ (W : Y.Opens) (n : ℕ), x ∈ W ∧ ∀ (p : M.ι) (l : H.ι) (O : Y.Opens) (_ : O ≤ W)
      (h : O ≤ ⊤ ⊓ (M.U p ⊓ H.U l)),
      rs Y (h.trans (inf_le_right.trans inf_le_right) : O ≤ H.U l) (σ.f l) ^ n *
        rs Y h (SecOn.twCoord a p l) = 0 := by
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (Set.mem_univ x))
  have hx : x ∈ (⊤ ⊓ (M.U q ⊓ H.U k) : Y.Opens) := ⟨trivial, hq, hk⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx (⊤ ⊓ (M.U q ⊓ H.U k) : Y.Opens).2
  have hWU' : W ≤ ⊤ ⊓ (M.U q ⊓ H.U k) := hWU
  have hWk : W ≤ H.U k := hWU'.trans (inf_le_right.trans inf_le_right)
  have hb : Y.basicOpen (rs Y hWk (σ.f k)) ≤ nonzeroLocus σ ⊓ (M.U q ⊓ H.U k) := by
    refine le_inf ?_ ((Y.basicOpen_le _).trans (hWU'.trans inf_le_right))
    refine le_trans ?_ (le_iSup (fun j => Y.basicOpen (σ.f j)) k)
    exact (Scheme.basicOpen_res Y (σ.f k) (homOfLE hWk).op).le.trans inf_le_right
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y hW
    (rs Y hWU' (SecOn.twCoord a q k)) (rs Y hWk (σ.f k)) (by
      have e := congrArg (fun y => rs Y hb (SecOn.twCoord y q k)) ha
      simp only [SecOn.twCoord_restrict, rs_rs] at e
      exact (rs_rs _ (Y.basicOpen_le _) _).trans (e.trans (map_zero _)))
  refine ⟨W, n, hxW, fun p l O hO h => ?_⟩
  have e := congrArg (rs Y hO) hn
  rw [map_mul, map_pow, rs_rs, rs_rs (U := H.U k) hWk hO (σ.f k), map_zero] at e
  have hl : O ≤ H.U l := h.trans (inf_le_right.trans inf_le_right)
  have hp : O ≤ M.U p := h.trans (inf_le_right.trans inf_le_left)
  have hq' : O ≤ M.U q := hO.trans (hWU'.trans (inf_le_right.trans inf_le_left))
  have e₁ : rs Y hl (σ.f l) = rs Y (le_inf hl (hO.trans hWk)) ((pw H d).g l k).val *
      rs Y (hO.trans hWk) (σ.f k) :=
    GlobalTheory.LB.sec_rel σ l k hl (hO.trans hWk) (le_inf hl (hO.trans hWk))
  rw [SecOn.twCoord_compat a p q l k h (hO.trans hWU') (le_inf hp hq') (le_inf hl (hO.trans hWk)),
    e₁, mul_pow, mul_mul_mul_comm, e, mul_zero]

theorem exists_pow_mul_twCoord_eq_zero : ∀ (Y : Scheme.{0}) (H M : LB Y) (d : ℤ) (σ : LB.Sec (pw H d)) (V : Y.Opens) (t : ℤ), H.IsLB → M.IsLB → V = nonzeroLocus σ → CompactSpace Y → ∀ a : SecOn (tw M H t) ⊤, SecOn.restrict _ (le_top : V ≤ ⊤) a = 0 → ∃ k : ℕ, ∀ (p : M.ι) (l : H.ι), rs Y (inf_le_right.trans inf_le_right : ⊤ ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (σ.f l) ^ k * SecOn.twCoord a p l = 0 := by
  rintro Y H M d σ V t hH hM rfl hY a ha
  choose W n hxW hn using exists_nhds_pow_mul_twCoord_eq_zero σ hH hM a ha
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : Y => (W x : Set Y))
    (fun x => (W x).2) fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩
  refine ⟨s.sup n, fun p l => ?_⟩
  refine GlobalTheory.LB.fun_ext_of_cover (fun x : s => W x ⊓ (⊤ ⊓ (M.U p ⊓ H.U l)))
    (fun _ => inf_le_right) (fun y hy => ?_) fun x => ?_
  · obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy', hy⟩
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) x.2)
    have e := hn x p l _ inf_le_left inf_le_right
    change rs Y _ _ = rs Y _ _
    rw [map_mul, map_pow, rs_rs (U := H.U l) _ _ (σ.f l), map_zero, hm,
      pow_add, _root_.mul_assoc, e, mul_zero]

end GlobalTheory.AbLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsPowMulMemRangeOfLocalDenominators
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem exists_dvd_pow_of_forall_prime_dvd {A : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] (a y : A) :
    y ≠ 0 → (∀ q, Prime q → q ∣ y → q ∣ a) → ∃ n : ℕ, y ∣ a ^ n := by
  refine UniqueFactorizationMonoid.induction_on_prime y ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro u hu _ _; exact ⟨0, hu.dvd⟩
  · intro z p hz hp ih _ h
    obtain ⟨n, hn⟩ := ih hz fun q hq hqz => h q hq (hqz.mul_left p)
    exact ⟨n + 1, by rw [pow_succ']; exact mul_dvd_mul (h p hp (dvd_mul_right _ _)) hn⟩

theorem exists_pow_mul_mem_range_of_local_denominators {A B : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [CommRing B] [IsDomain B] (φ : A →+* B)
    (hφ : Function.Injective φ) (W : Set (PrimeSpectrum A)) (hW : W.Nonempty) (a : A)
    (ha : ∀ (q : A) (p : PrimeSpectrum A), Prime q → p.asIdeal = Ideal.span {q} → p ∉ W → q ∣ a)
    (v : B) (hv : ∀ p ∈ W, ∃ s, s ∉ p.asIdeal ∧ ∃ x, φ x = φ s * v) :
    ∃ (n : ℕ) (x : A), φ x = φ a ^ n * v := by
  obtain ⟨p₀, hp₀⟩ := hW
  obtain ⟨s, hs, x, e⟩ := hv p₀ hp₀
  have hs0 : s ≠ 0 := fun h => hs (h ▸ p₀.asIdeal.zero_mem)
  obtain ⟨y, x', c, hrel, rfl, rfl⟩ := UniqueFactorizationMonoid.exists_reduced_factors s hs0 x
  have hc : c ≠ 0 := left_ne_zero_of_mul hs0
  have hy : y ≠ 0 := right_ne_zero_of_mul hs0
  have e' : φ x' = φ y * v := by
    rw [map_mul, map_mul, _root_.mul_assoc] at e
    exact mul_left_cancel₀ ((map_ne_zero_iff _ hφ).mpr hc) e
  obtain ⟨n, z, hz⟩ := exists_dvd_pow_of_forall_prime_dvd a y hy fun q hq hqy => by
    refine ha q ⟨Ideal.span {q}, (Ideal.span_singleton_prime hq.ne_zero).2 hq⟩ hq rfl fun hm => ?_
    obtain ⟨t, ht, w, ew⟩ := hv _ hm
    refine ht (Ideal.mem_span_singleton.2 (hqy.trans (hrel.dvd_of_dvd_mul_right ⟨w, hφ ?_⟩)))
    rw [map_mul, map_mul, e', ew, mul_left_comm]
  refine ⟨n, z * x', ?_⟩
  rw [← map_pow, hz, map_mul, map_mul, e']
  ring

theorem exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [UniqueFactorizationMonoid A] (U : (Spec (CommRingCat.of A)).Opens), IsAffineOpen U → (U : Set (Spec (CommRingCat.of A))).Nonempty → ∃ a : A, U = PrimeSpectrum.basicOpen a := by
  classical
  intro A _ _ _ _ U hU hne
  have hloc : ∀ p : PrimeSpectrum A, p ∈ U → ∃ f : A,
      p ∈ PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ U := by
    intro p hp
    obtain ⟨_, ⟨f, rfl⟩, h1, h2⟩ :=
      (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open hp U.isOpen
    exact ⟨f, h1, h2⟩
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨f, hf, hfU⟩ := hloc p₀ hp₀
  have hf0 : f ≠ 0 := fun h => hf (h ▸ p₀.asIdeal.zero_mem)
  let a : A := ((UniqueFactorizationMonoid.factors f).filter fun q =>
    ∃ p : PrimeSpectrum A, p.asIdeal = Ideal.span {q} ∧ p ∉ U).prod
  have ha : ∀ (q : A) (p : PrimeSpectrum A), Prime q → p.asIdeal = Ideal.span {q} →
      p ∉ U → q ∣ a := by
    intro q p hq hp hpU
    have hqf : q ∣ f := by
      rw [← Ideal.mem_span_singleton, ← hp]
      by_contra h
      exact hpU (hfU h)
    obtain ⟨r, hr, hqr⟩ :=
      UniqueFactorizationMonoid.exists_mem_factors_of_dvd hf0 hq.irreducible hqf
    refine hqr.dvd.trans (Multiset.dvd_prod (Multiset.mem_filter.2 ⟨hr, p, ?_, hpU⟩))
    rw [hp]
    exact Ideal.span_singleton_eq_span_singleton.2 hqr
  refine ⟨a, le_antisymm ?_ ?_⟩
  · intro p hp hpa
    have := p.isPrime
    obtain ⟨q, hq, hqp⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem p.isPrime _).1 hpa
    obtain ⟨-, p', hp', hp'U⟩ := Multiset.mem_filter.1 hq
    obtain ⟨g, hg, hgU⟩ := hloc p hp
    refine hp'U (hgU fun h => hg ?_)
    have h' : g ∈ p'.asIdeal := h
    rw [hp'] at h'
    exact (Ideal.span_singleton_le_iff_mem _).2 hqp h'
  · have : Nonempty U := ⟨⟨_, hp₀⟩⟩
    have hinj := map_injective_of_isIntegral (Spec (CommRingCat.of A)) (homOfLE (le_top : U ≤ ⊤))
    let φ : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of A), U) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    have hφ : Function.Injective φ :=
      hinj.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1
    have key : ∀ (v : Γ(Spec (CommRingCat.of A), U)) (p : PrimeSpectrum A), p ∈ U →
        ∃ s, s ∉ p.asIdeal ∧ ∃ a, φ a = φ s * v := by
      intro v p hp
      let x : Spec (CommRingCat.of A) := p
      obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (S := (Spec.structureSheaf A).presheaf.stalk p)
        p.asIdeal.primeCompl ((Spec (CommRingCat.of A)).presheaf.germ U x hp v)
      refine ⟨s, s.2, a, germ_injective_of_isIntegral _ x hp ?_⟩
      have hg : ∀ a : A, (Spec (CommRingCat.of A)).presheaf.germ U x hp (φ a) =
          algebraMap A ((Spec.structureSheaf A).presheaf.stalk p) a := by
        intro a
        exact ((Spec (CommRingCat.of A)).presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hp
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)).trans rfl
      rw [map_mul, hg, hg]
      exact e.symm.trans (mul_comm _ _)
    have key2 : ∀ v : Γ(Spec (CommRingCat.of A), U), ∃ (n : ℕ) (x : A), φ x = φ a ^ n * v :=
      fun v => exists_pow_mul_mem_range_of_local_denominators φ.hom hφ
        (U : Set (Spec (CommRingCat.of A))) ⟨p₀, hp₀⟩ a ha v (key v)
    intro p hpa
    by_contra hpU
    have hspan : Ideal.span (φ '' {g : A | PrimeSpectrum.basicOpen g ≤ U}) = ⊤ := by
      rw [← hU.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨g, hg, hgU⟩ := hloc x hx
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨φ g, g, hgU, rfl⟩, ?_⟩
      have e : (Spec (CommRingCat.of A)).basicOpen (φ g) = U ⊓ PrimeSpectrum.basicOpen g := by
        rw [← basicOpen_eq_of_affine (R := CommRingCat.of A) g]
        exact Scheme.basicOpen_res _ _ (homOfLE (le_top : U ≤ ⊤)).op
      show x ∈ (Spec (CommRingCat.of A)).basicOpen (φ g)
      rw [e]
      exact ⟨hx, hg⟩
    have hall : ∀ v ∈ Ideal.span (φ '' {g : A | PrimeSpectrum.basicOpen g ≤ U}),
        ∃ (n : ℕ) (x : A), x ∈ p.asIdeal ∧ φ x = φ a ^ n * v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨g, hg, rfl⟩ := hv
        refine ⟨0, g, ?_, by simp⟩
        by_contra h
        exact hpU (hg h)
      | zero => exact ⟨0, 0, p.asIdeal.zero_mem, by simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨n, x, hx, e⟩ := hv
        obtain ⟨m, y, hy, e'⟩ := hw
        refine ⟨n + m, a ^ m * x + a ^ n * y,
          p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hx) (p.asIdeal.mul_mem_left _ hy), ?_⟩
        rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, e, e']
        ring
      | smul c v _ hv =>
        obtain ⟨n, x, hx, e⟩ := hv
        obtain ⟨m, y, e'⟩ := key2 c
        refine ⟨n + m, y * x, p.asIdeal.mul_mem_left _ hx, ?_⟩
        rw [map_mul, e, e', smul_eq_mul]
        ring
    obtain ⟨n, x, hx, e⟩ := hall 1 (hspan ▸ Submodule.mem_top)
    rw [_root_.mul_one, ← map_pow] at e
    rw [hφ e] at hx
    exact hpa (p.isPrime.mem_of_pow_mem n hx)

end GlobalTheory
end

