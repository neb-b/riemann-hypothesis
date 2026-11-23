module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenOfSpecializesIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

open Set Topology

namespace GlobalTheory.SpecGenClopen

theorem isClosed_of_stable (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Set X)
    (hs : StableUnderSpecialization T) (hg : StableUnderGeneralization T) : IsClosed T := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : TopologicalSpace.NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let T' : Set (U : Set X) := Subtype.val ⁻¹' T
  have key : ∀ Z : Set (U : Set X), IsIrreducible Z → (Z ∩ T').Nonempty → Z ⊆ T' := by
    rintro Z hZ ⟨t, htZ, htT⟩ z hz
    have hI : IsIrreducible (closure (Subtype.val '' Z : Set X)) :=
      (hZ.image _ continuous_subtype_val.continuousOn).closure
    obtain ⟨g₀, hg₀⟩ := QuasiSober.sober hI isClosed_closure
    have h1 : g₀ ⤳ (t : X) := hg₀.specializes (subset_closure ⟨t, htZ, rfl⟩)
    have h2 : g₀ ⤳ (z : X) := hg₀.specializes (subset_closure ⟨z, hz, rfl⟩)
    exact hs h2 (hg h1 htT)
  have hT' : T' = ⋃ Z ∈ {Z ∈ irreducibleComponents (U : Set X) | (Z ∩ T').Nonempty}, Z := by
    ext t
    refine ⟨fun ht => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents t,
      ⟨t, mem_irreducibleComponent, ht⟩⟩ mem_irreducibleComponent, fun ht => ?_⟩
    obtain ⟨Z, ⟨hZ, hZT⟩, htZ⟩ := Set.mem_iUnion₂.1 ht
    exact key Z hZ.1 hZT htZ
  have hc : IsClosed T' := by
    rw [hT']
    exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (by exact fun _ h => h.1)).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  refine ⟨Subtype.val '' T'ᶜ, ?_, U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hc.isOpen_compl, ⟨x, hxU⟩, hx, rfl⟩
  rintro _ ⟨t, ht, rfl⟩
  exact ht

theorem isClopen_of_specializes_iff : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Z : Set X),
    (∀ x y : X, x ⤳ y → (x ∈ Z ↔ y ∈ Z)) → IsClopen Z := by
  intro X _ Z h
  have hs : StableUnderSpecialization Z := fun x y hxy hx => (h x y hxy).1 hx
  have hg : StableUnderGeneralization Z := fun x y hxy hx => (h y x hxy).2 hx
  exact ⟨isClosed_of_stable X Z hs hg, isClosed_compl_iff.1 (isClosed_of_stable X Zᶜ
    (stableUnderSpecialization_compl_iff.2 hg) (stableUnderGeneralization_compl_iff.2 hs))⟩

end GlobalTheory.SpecGenClopen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GaloisCartDesc

theorem epi_of_isGaloisCover {X Y : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) : Epi π := by
  refine ⟨fun {Z} g₁ g₂ e ↦ ?_⟩
  obtain ⟨f', -, hu⟩ := h.existsUnique_desc (π ≫ g₁) (fun a ↦ by rw [← Category.assoc, h.inv])
  exact (hu g₁ rfl).trans (hu g₂ e.symm).symm

theorem epi_pullback_fst {X Y : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {T : Scheme.{0}} (t : T ⟶ Y) : Epi (pullback.fst t π) := by
  let ρ' : Ga → (pullback t π ⟶ pullback t π) := fun a ↦
    pullback.map t π t π (𝟙 _) (ρ a) (𝟙 _) (by simp) (by simp [h.inv])
  have hg : GlobalTheory.ZM.IsGaloisCover Ga ρ' (pullback.fst t π) :=
    by
      let hp := (IsPullback.of_hasPullback t π).flip
      have hu : ∀ a, ρ' a ≫ pullback.snd t π = pullback.snd t π ≫ ρ a :=
        fun a ↦ by simp only [ρ', pullback.map, pullback.lift_snd]
      exact ((GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ h).2.2 _ _ _ _ _ _ hu hp.w).2 hp
        (fun a ↦ by simp only [ρ', pullback.map, pullback.lift_fst, Category.comp_id])
  exact epi_of_isGaloisCover hg

theorem isGrpPullback_of_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y)
    (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left)
    (ψ : A'.left ⟶ B.left) (φ : A.left ⟶ B.left), GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ →
    IsGrpPullback A' B (π₁ ≫ f) ψ → φ₁ ≫ φ = ψ → IsGrpPullback A B f φ := by
  intro S S₁ Y π₁ Ga _ ρ₁ f A' A B _ _ _ φ₁ ψ φ hG hφ₁ hψ hφ

  let τ : Ga → (A'.left ⟶ A'.left) := fun a ↦
    hφ₁.1.lift φ₁ (A'.hom ≫ ρ₁ a) (by rw [hφ₁.1.w, Category.assoc, hG.inv])
  have hτ₁ : ∀ a, τ a ≫ φ₁ = φ₁ := fun a ↦ hφ₁.1.lift_fst _ _ _
  have hτ₂ : ∀ a, τ a ≫ A'.hom = A'.hom ≫ ρ₁ a := fun a ↦ hφ₁.1.lift_snd _ _ _
  have gφ₁ : GlobalTheory.ZM.IsGaloisCover Ga τ φ₁ := ((GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hG).2.2 _ _ _ _ _ _ hτ₂ hφ₁.1.flip.w).2 hφ₁.1.flip hτ₁
  have eφ₁ : Epi φ₁ := epi_of_isGaloisCover gφ₁

  have w : φ ≫ B.hom = A.hom ≫ f := by
    rw [← cancel_epi φ₁, reassoc_of% hφ, hψ.1.w, ← reassoc_of% hφ₁.1.w]

  let q : A'.left ⟶ pullback B.hom f := pullback.lift ψ (A'.hom ≫ π₁) (by rw [hψ.1.w, Category.assoc])
  have hq₁ : q ≫ pullback.fst B.hom f = ψ := pullback.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd B.hom f = A'.hom ≫ π₁ := pullback.lift_snd _ _ _
  have hsq : IsPullback q A'.hom (pullback.snd B.hom f) π₁ := by
    refine IsPullback.of_right ?_ hq₂ (IsPullback.of_hasPullback B.hom f)
    rw [hq₁]
    exact hψ.1
  have hτq : ∀ a, τ a ≫ q = q := fun a ↦ by
    apply pullback.hom_ext
    · rw [Category.assoc, hq₁, ← hφ, reassoc_of% hτ₁ a]
    · rw [Category.assoc, hq₂, reassoc_of% hτ₂ a, hG.inv]
  have gq : GlobalTheory.ZM.IsGaloisCover Ga τ q := ((GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hG).2.2 _ _ _ _ _ _ hτ₂ hsq.flip.w).2 hsq.flip hτq
  have eq : Epi q := epi_of_isGaloisCover gq
  obtain ⟨d, hd, -⟩ := gq.existsUnique_desc φ₁ hτ₁
  let c : A.left ⟶ pullback B.hom f := pullback.lift φ A.hom w
  have hc : φ₁ ≫ c = q := by
    apply pullback.hom_ext
    · simp only [c, Category.assoc, hq₁]
      rw [pullback.lift_fst, hφ]
    · simp only [c, Category.assoc, hq₂]
      rw [pullback.lift_snd, hφ₁.1.w]
  have hcd : c ≫ d = 𝟙 _ := by rw [← cancel_epi φ₁, reassoc_of% hc, hd, Category.comp_id]
  have hdc : d ≫ c = 𝟙 _ := by rw [← cancel_epi q, reassoc_of% hd, hc, Category.comp_id]
  let i : A.left ≅ pullback B.hom f := ⟨c, d, hcd, hdc⟩
  refine ⟨IsPullback.of_iso_pullback ⟨w⟩ i (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), ?_⟩

  intro T x y x₀ y₀ hx hy
  let e : pullback T.hom π₁ ⟶ T.left := pullback.fst T.hom π₁
  have ee : Epi e := epi_pullback_fst hG T.hom
  let T₁ : Over S₁ := Over.mk (pullback.snd T.hom π₁)
  let j : Over.mk (T₁.hom ≫ π₁) ⟶ T := Over.homMk e (by simp [T₁, e, pullback.condition])
  let j' : Over.mk (T₁.hom ≫ π₁ ≫ f) ⟶ Over.mk (T.hom ≫ f) :=
    Over.homMk e (by simp [T₁, e, pullback.condition_assoc])
  have lift : ∀ z : T ⟶ A, ∃ z₁ : T₁ ⟶ A', z₁.left ≫ φ₁ = e ≫ z.left := fun z ↦
    ⟨Over.homMk (hφ₁.1.lift (e ≫ z.left) (pullback.snd T.hom π₁)
      (by simp [e, pullback.condition])) (hφ₁.1.lift_snd _ _ _), hφ₁.1.lift_fst _ _ _⟩
  obtain ⟨x₁, hx₁⟩ := lift x
  obtain ⟨y₁, hy₁⟩ := lift y
  have a₁ : ((j ≫ x) * (j ≫ y)).left = (x₁ * y₁).left ≫ φ₁ :=
    hφ₁.2 T₁ x₁ y₁ (j ≫ x) (j ≫ y) (by simp [j, hx₁]) (by simp [j, hy₁])
  have a₂ : ((j' ≫ x₀) * (j' ≫ y₀)).left = (x₁ * y₁).left ≫ ψ :=
    hψ.2 T₁ x₁ y₁ (j' ≫ x₀) (j' ≫ y₀) (by simp [j', hx, ← hφ, reassoc_of% hx₁])
      (by simp [j', hy, ← hφ, reassoc_of% hy₁])
  rw [← MonObj.comp_mul] at a₁ a₂
  rw [← cancel_epi e]
  have b₁ : e ≫ (x * y).left = (x₁ * y₁).left ≫ φ₁ := by simpa [j] using a₁
  have b₂ : e ≫ (x₀ * y₀).left = (x₁ * y₁).left ≫ ψ := by simpa [j'] using a₂
  rw [b₂, reassoc_of% b₁, hφ]

end GlobalTheory.GaloisCartDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousCofactor
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.CofactorHom

theorem wcomp_mul_of_left {σ F : Type} [Field F] (w : σ → ℕ) (n : ℕ) {P : MvPolynomial σ F} {k : ℕ}
    (hP : IsWeightedHomogeneous w P k) (Q : MvPolynomial σ F) :
    weightedHomogeneousComponent w n (P * Q) =
      if k ≤ n then P * weightedHomogeneousComponent w (n - k) Q else 0 := by
  classical
  let := weightedGradedAlgebra F w
  have h := DirectSum.coe_decompose_mul_of_left_mem (weightedHomogeneousSubmodule F w) (a := P) (b := Q) n
    ((mem_weightedHomogeneousSubmodule F w k P).2 hP)
  have e : ∀ (m : ℕ) (R : MvPolynomial σ F),
      ((DirectSum.decompose (weightedHomogeneousSubmodule F w) R m : weightedHomogeneousSubmodule F w m) :
        MvPolynomial σ F) = weightedHomogeneousComponent w m R :=
    fun m R => weightedDecomposition.decompose'_apply F w R m
  rw [e, e] at h
  exact h

theorem weight_add_of_mul {σ F : Type} [Field F] (w : σ → ℕ) {P Q : MvPolynomial σ F} {k m : ℕ}
    (hPQ : P * Q ≠ 0) (hP : IsWeightedHomogeneous w P k) (hm : IsWeightedHomogeneous w (P * Q) m)
    (s : σ →₀ ℕ) (hs : s ∈ Q.support) : k + Finsupp.weight w s = m := by
  classical
  have hP0 : P ≠ 0 := left_ne_zero_of_mul hPQ
  set j := Finsupp.weight w s
  have hc : weightedHomogeneousComponent w j Q ≠ 0 := by
    intro h0
    have := congrArg (AddMonoidAlgebra.coeff · s) h0
    apply (mem_support_iff.mp hs)
    simpa only [coeff_weightedHomogeneousComponent, j, ite_true,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using this

  have hne : weightedHomogeneousComponent w (k + j) (P * Q) ≠ 0 := by
    simp only [wcomp_mul_of_left w (k + j) hP Q, Nat.le_add_right, ite_true,
      Nat.add_sub_cancel_left]
    exact mul_ne_zero hP0 hc
  by_contra hkm
  exact hne (hm.weightedHomogeneousComponent_ne (k + j) hkm)

end GlobalTheory.CofactorHom


open GlobalTheory.CofactorHom in
theorem GlobalTheory.HSShort.isMultiHomogeneous_cofactor :
    ∀ (F : Type) [Field F] (B N : ℕ) (a a₁ : Fin B → ℕ) (G G' : MvPolynomial (Fin B × Fin N) F),
      G * G' ≠ 0 → IsMultiHomogeneous a (G * G') → IsMultiHomogeneous a₁ G →
        ∃ a' : Fin B → ℕ, IsMultiHomogeneous a' G' ∧ ∀ i, a₁ i + a' i = a i := by
  intro F _ B N a a₁ G G' h0 ha ha₁
  rw [isMultiHomogeneous_iff_forall_weighted_lh0BlockWt] at ha ha₁
  have key : ∀ b, ∀ s ∈ G'.support, a₁ b + ∑ j : Fin N, s (b, j) = a b := fun b s hs => by
    rw [← weight_lh0BlockWt_apply]
    exact weight_add_of_mul _ h0 (ha₁ b) (ha b) s hs
  obtain ⟨s₀, hs₀⟩ : ∃ s, s ∈ G'.support := by
    by_contra hno
    push Not at hno
    apply h0
    rw [show G' = 0 from by
      ext s; by_contra hc; exact hno s (mem_support_iff.mpr hc), mul_zero]
  refine ⟨fun b => a b - a₁ b, fun s hs b => ?_, fun i => ?_⟩
  · have := key b s hs
    show _ = a b - a₁ b
    omega
  · have := key i s₀ hs₀
    show a₁ i + (a i - a₁ i) = a i
    omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousProd
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice

namespace GlobalTheory.ZeroCycleHt

theorem linSubst_mul {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (f g : MvPolynomial (Fin B × Fin N) R) : linSubst M (f * g) = linSubst M f * linSubst M g := by
  simp [linSubst]

theorem exists_rightInv {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Function.Surjective w.mulVec) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  classical
  choose x hx using fun j : Fin N => hw (Pi.single j 1)
  refine ⟨Matrix.of fun k j => x j k, ?_⟩
  ext i j
  have := congrFun (hx j) i
  simp only [Matrix.mulVec, dotProduct] at this
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [this, Pi.single_apply]

theorem formHeight_mul {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ δ' : ℕ)
    {w : Matrix (Fin N) (Fin n) F} {P : Matrix (Fin n) (Fin N) F} (hP : w * P = 1)
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0) {a a' : Fin B → ℕ}
    {f g : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (hg : g ≠ 0)
    (ha : IsMultiHomogeneous a f) (ha' : IsMultiHomogeneous a' g) :
    formHeight (δ + δ') w A (f * g) = formHeight δ w A f + formHeight δ' w A g := by
  have hlf := GlobalTheory.HeightUnique.linSubst_ne_zero hP hf
  have hlg := GlobalTheory.HeightUnique.linSubst_ne_zero hP hg
  have hfin : ∑ᶠ v : FinitePlace F, Real.log (gaussAbs v (linSubst w (f * g))) =
      ∑ᶠ v : FinitePlace F, Real.log (gaussAbs v (linSubst w f)) +
        ∑ᶠ v : FinitePlace F, Real.log (gaussAbs v (linSubst w g)) := by
    rw [← finsum_add_distrib (gauss_abs_log_support_finite _ hlf) (gauss_abs_log_support_finite _ hlg)]
    refine finsum_congr fun v => ?_
    rw [linSubst_mul, gauss_abs_mul v _ _ hlf hlg,
      Real.log_mul (gauss_abs_pos_of_ne_zero v _ hlf).ne' (gauss_abs_pos_of_ne_zero v _ hlg).ne']
  have hne : ∀ (σ : F →+* ℂ) {h : MvPolynomial (Fin B × Fin N) F}, h ≠ 0 →
      linSubst (A σ) (MvPolynomial.map σ h) ≠ 0 := fun σ h hh =>
    GlobalTheory.HeightUnique.linSubst_ne_zero ((A σ).mul_nonsing_inv (hA σ).isUnit) fun h0 =>
      hh (MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero]))
  have hinf : ∀ σ : F →+* ℂ, blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ (f * g))) =
      blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) +
        blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ g)) := by
    intro σ
    rw [map_mul, linSubst_mul]
    exact sphere_mean_mul_multihomogeneous Closed.sphereLogIntegrable B N a a' _ _ (hne σ hf) (hne σ hg)
      (GlobalTheory.HeightUnique.linSubst_homog _ (isMultiHomogeneous_map_ring a f ha σ))
      (GlobalTheory.HeightUnique.linSubst_homog _ (isMultiHomogeneous_map_ring a' g ha' σ))
  unfold formHeight
  rw [hfin]
  simp only [hinf, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_add]
  ring

theorem formHeight_one {F : Type} [Field F] [NumberField F] {B N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) :
    formHeight 0 w A (1 : MvPolynomial (Fin B × Fin N) F) = 0 := by
  have h1 : ∀ v : FinitePlace F, gaussAbs v (1 : MvPolynomial (Fin B × Fin n) F) = 1 := fun v => by
    simpa using GlobalTheory.HeightUnique.gaussAbs_C (σ := Fin B × Fin n) v (1 : F)
  unfold formHeight
  simp [linSubst, h1, blockSphereMean]

end GlobalTheory.ZeroCycleHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRankGe
section
open ValuativeRel Matrix

theorem GlobalTheory.isOpen_setOf_le_rank_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (s : ℕ), IsOpen {X : Matrix A D k | s ≤ X.rank} := by
  intro k _ _ _ _ A D _ _ _ _ s
  rw [isOpen_iff_mem_nhds]
  intro X hX
  obtain ⟨H, Q, hHQ⟩ := _root_.GlobalTheory.rank_frame_exists k A D X
  have hc : Continuous fun Y : Matrix A D k => (H * Y * Q).det :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
  have hopen : IsOpen {Y : Matrix A D k | (H * Y * Q).det ≠ 0} :=
    isOpen_ne_fun hc continuous_const
  filter_upwards [hopen.mem_nhds (by simp [hHQ])] with Y hY
  replace hY : (H * Y * Q).det ≠ 0 := hY
  show s ≤ Y.rank
  refine le_trans hX ?_
  have hu : IsUnit (H * Y * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hY)
  have hr : (H * Y * Q).rank = X.rank := by
    rw [Matrix.rank_of_isUnit _ hu]; simp
  calc X.rank = (H * Y * Q).rank := hr.symm
    _ ≤ (H * Y).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Y.rank := Matrix.rank_mul_le_right _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfIsCompAlongSplit
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphBC

open GlobalTheory.PRep GlobalTheory.DefU

theorem isSpherical_of_isCompAlong_split {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X)
    (hc : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ) (hu : IsUnramU π w) :
    GlobalTheory.LGrp.IsSpherical σ (GlobalTheory.LFun.KGL w (n := n)) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  have hp : Function.Surjective ((cLoc w).comp (locU n w).subtype) := fun g =>
    ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
  obtain ⟨φ, hφ, hφ0, hφK⟩ := hu
  by_contra hns
  have hfix : ∀ v, (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), σ k v = v) → v = 0 := by
    intro v hv
    by_contra hv0
    exact hns ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩)
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hc
  let Ψ : AutSub E n := ⟨π, hπ⟩
  have hirr : Representation.IsIrreducible (σ.comp ((cLoc w).comp (locU n w).subtype)) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype)) (Ψ.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V X X Ψ.rep (locU n w).subtype
    (σ.comp ((cLoc w).comp (locU n w).subtype)) (σ.comp ((cLoc w).comp (locU n w).subtype))
    Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype))
      (Ψ.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA E n → ℂ) := fun i => π.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.comp ((cLoc w).comp (locU n w).subtype)) g u) =
      (RU E n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype))
        (Ψ.rep.comp (locU n w).subtype), LinearMap.range i.toLinearMap).map π.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this
  have key := GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ((RU E n).comp (locU n w).subtype)
    (σ.comp ((cLoc w).comp (locU n w).subtype)) hirr fi hfi
    (((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype) : Subgroup (locU n w)) : Set (locU n w)) ⊥
    (fun i v hv => by
      have hv' : v = 0 := hfix v fun k hk => by
        obtain ⟨x, rfl⟩ := hp k
        exact hv x hk
      rw [hv', map_zero]
      exact Submodule.zero_mem _)
    (fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) φ (fun k hk => hφK k.1 k.2 hk) hmem
  exact hφ0 ((Submodule.mem_bot ℂ).1 key)

theorem isSpherical_of_isUnramU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
      (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ)
      (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)),
      GlobalTheory.BcSpeh.Parts π a d h P ρ m →
      (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) →
      (∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))) →
      ∀ w, IsUnramU π w → ∀ i (τ : SmIrr (GL (Fin (a i)) (w.adicCompletion E))), (P i).IsLocComp w τ →
        GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w (n := (a i))) := by
  intro E _ _ _ hE n π hπ c a d h P ρ m σ hp hsh hsplit w hu i τ hτ
  suffices hB : ∃ B, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ B by
    obtain ⟨B, hB⟩ := hB
    have h1 := (GlobalTheory.BcSpehCompare.hasSat_iff (hp.loc i w) B).2 hB
    exact ((GlobalTheory.BcSpehCompare.hasSat_iff hτ B).1 h1).1
  by_cases hw : IsSplitAt w
  · have hc := hsplit w hw
    have hs : GlobalTheory.LGrp.IsSpherical (locProd h w (σ · w)) (GlobalTheory.LFun.KGL w (n := n)) :=
      isSpherical_of_isCompAlong_split hπ hw _ hc hu
    have hsm : GlobalTheory.PRep.IsSmooth (locProd h w (σ · w)) := GlobalTheory.SmGL.isSmooth_parInd _ _
    have hirr : (locProd h w (σ · w)).IsIrreducible := hc.1
    obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible hsm hirr hs
    obtain ⟨S, hS, -⟩ := GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hp.pos i).2)
      (fun i => (hsh i w).2.2) T hT
    exact ⟨S i, hS i⟩
  · obtain ⟨s, ϖ, q, α, h1, h2, h3⟩ := GlobalTheory.BcSpehCompare.exists_hasSatAt hE hπ hw hu
    obtain ⟨S, hS, -⟩ := hp.inert w s ϖ q h1 h2 α h3
    exact ⟨S i, hS i⟩

end GlobalTheory.SphBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemRelationOfGenericPointStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSystem_relation_of_generic_point : ∀ (F : Type) [Field F] (S : LinSys F), AlgebraicGeometry.IsIntegral S.Y → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (η : S.Y), IsGenericPoint η Set.univ → ∀ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) → S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η)) (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ) = 0 → ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.Adelic.GenericRel.relation_of_generic | exact GlobalTheory.Adelic.GenericRel.relation_of_generic | (intros; apply GlobalTheory.Adelic.GenericRel.relation_of_generic <;> assumption)
end

