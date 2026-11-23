module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CyclicIdeal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.SecCyclic
open GlobalTheory.AbLaw.Seesaw

theorem coker_equiv {R : Type} [CommRing R] {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (v₀ : Fin a → R)
    (k : Fin a) (hk : IsUnit (v₀ k))
    (hker : ∀ (R' : Type) [CommRing R'] (g : R →+* R'),
      ∀ w, (D.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀)) :
    Nonempty (((Fin a → R) ⧸ LinearMap.range D.transpose.mulVecLin) ≃ₗ[R]
      (R ⧸ Ideal.span (Set.range (D.mulVec v₀)))) := by
  classical
  set N := LinearMap.range D.transpose.mulVecLin with hN
  set I := Ideal.span (Set.range (D.mulVec v₀)) with hI
  have hrow : ∀ i, ∑ j, D i j • N.mkQ (Pi.single j 1) = 0 := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    refine (Submodule.Quotient.mk_eq_zero N).2 ⟨Pi.single i 1, ?_⟩
    funext j
    simp [Pi.single_apply, Finset.sum_apply]
  obtain ⟨c, hc⟩ := hker (TrivSqZeroExt R ((Fin a → R) ⧸ N)) (TrivSqZeroExt.inlHom R ((Fin a → R) ⧸ N))
    (fun j => TrivSqZeroExt.inr (N.mkQ (Pi.single j 1))) (by
      funext i
      change ∑ j, TrivSqZeroExt.inl (D i j) * TrivSqZeroExt.inr (N.mkQ (Pi.single j 1)) = (0 : TrivSqZeroExt R ((Fin a → R) ⧸ N))
      have := congrArg (TrivSqZeroExt.inrHom R ((Fin a → R) ⧸ N)) (hrow i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at this
      exact (Finset.sum_congr rfl fun j _ => TrivSqZeroExt.inl_mul_inr _ _).trans this)
  have he : ∀ j, N.mkQ (Pi.single j 1) = v₀ j • c.snd := fun j => by
    have := congrArg TrivSqZeroExt.snd (congrFun hc j)
    change _ = (c * TrivSqZeroExt.inl (v₀ j)).snd at this
    rw [_root_.mul_comm, TrivSqZeroExt.inl_mul_eq_smul, TrivSqZeroExt.snd_smul] at this
    exact this
  have hx : ∀ x : Fin a → R, N.mkQ x = (x ⬝ᵥ v₀) • c.snd := fun x => by
    have : x = ∑ j, x j • (Pi.single j 1 : Fin a → R) := by
      funext j
      simp [Pi.single_apply, Finset.sum_apply]
    conv_lhs => rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, he, smul_smul, dotProduct, Finset.sum_smul]
  have hIq : ∀ r ∈ I, r • c.snd = 0 := fun r hr => by
    refine Submodule.span_induction (p := fun r _ => r • c.snd = 0) ?_ (zero_smul _ _) ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩
      rw [← hrow i]
      simp only [he, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    · intro x y _ _ h₁ h₂
      rw [add_smul, h₁, h₂, add_zero]
    · intro s x _ h
      rw [smul_eq_mul, mul_smul, h, smul_zero]
  let φ : (Fin a → R) →ₗ[R] R ⧸ I := I.mkQ ∘ₗ (dotProductBilin R R).flip v₀
  have hφ : ∀ x, φ x = I.mkQ (x ⬝ᵥ v₀) := fun _ => rfl
  have hs : Function.Surjective φ := fun y => by
    obtain ⟨r, rfl⟩ := I.mkQ_surjective y
    obtain ⟨u, hu⟩ := hk
    refine ⟨Pi.single k (r * u⁻¹.val), ?_⟩
    rw [hφ, single_dotProduct, ← hu, Units.inv_mul_cancel_right]
  have hk' : N = LinearMap.ker φ := by
    ext x
    rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
      exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩)
    · intro h
      exact (Submodule.Quotient.mk_eq_zero N).1 ((hx x).trans (hIq _ h))
  exact ⟨(Submodule.quotEquivOfEq _ _ hk').trans (φ.quotKerEquivOfSurjective hs)⟩

theorem cyclic_ideal : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → ∀ P : Perf f M, UniversallyClosed f → Surjective f → ∀ (K : Type) [Field K] (g₀ : R →+* K), IsLocalHom g₀ → ∀ (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom → Triv (M.pull π₀) → ∃ I : Ideal R, Nonempty (((Fin P.a → R) ⧸ LinearMap.range P.D₀.transpose.mulVecLin) ≃ₗ[R] (R ⧸ I)) ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → (Triv (M.pull π) ↔ I ≤ RingHom.ker g) := by
  intro R _ _ X f M hM P hcl hsurj K _ g₀ hloc X₀ π₀ f₀ h₀ hb ht
  obtain ⟨v, hv, hu, hline⟩ := loc_of_triv P h₀ hM ht
  have unit_of : ∀ r : R, g₀ r ≠ 0 → IsUnit r := fun r hr => hloc.map_nonunit r hr.isUnit
  let z : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  have unit_cst : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
      ∀ (c : R') (w : Fin P.a → R'), (∀ i, IsUnit (loc P π f' (c • w) i)) → IsUnit c := by
    intro R' _ g X' π f' h c w H
    by_contra hc
    obtain ⟨m, hm, hcm⟩ := exists_max_ideal_of_mem_nonunits hc
    have : Surjective f' := MorphismProperty.of_isPullback h hsurj
    obtain ⟨y, hy⟩ := f'.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have h₁ := H i
    rw [loc_smul] at h₁
    have h₂ := (mem_basicOpen_cst f' _ c hi).1 (mem_of_isUnit (isUnit_of_mul_isUnit_left h₁) hi)
    rw [hy] at h₂
    exact h₂ hcm
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (unit_cst K g₀ X₀ π₀ f₀ h₀ 0 0 (by rwa [smul_zero]))
  obtain ⟨δ, v₀, hδ, hker₀⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline hb.2)
  have hker : ∀ (R' : Type) [CommRing R'] (g : R →+* R'),
      ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀) :=
    fun R' _ g => hker₀ R' g ((unit_of δ hδ).map g)
  obtain ⟨c₀, hc₀⟩ := hker K g₀ v hv
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  have hk' : IsUnit (v₀ k) := unit_of _ fun h0 => hk (by
    rw [hc₀]
    change c₀ * g₀ (v₀ k) = 0
    rw [h0, mul_zero])
  let G : X.Opens := ⨆ i, X.basicOpen (loc₀ P v₀ i)
  have hZ : IsClosed (f '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hp : Spec.map (CommRingCat.ofHom g₀) z ∈ (f '' (G : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, hfx⟩
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₀ x z hfx
    obtain ⟨i, hi⟩ := exists_mem P (π₀ y)
    have h₁ := hu i
    rw [hc₀, loc_smul, loc_comp P h₀] at h₁
    have h₂ := mem_of_isUnit (isUnit_of_mul_isUnit_right h₁) (y := y) hi
    rw [← Scheme.preimage_basicOpen] at h₂
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩)
  obtain ⟨_, ⟨r₁, rfl⟩, hr₁, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp hZ.isOpen_compl
  have hr₁' : IsUnit r₁ := unit_of r₁ hr₁
  refine ⟨Ideal.span (Set.range (P.D₀.mulVec v₀)), coker_equiv P.D₀ v₀ k hk' hker,
    fun R' _ g X' π f' h => ?_⟩
  have hI : Ideal.span (Set.range (P.D₀.mulVec v₀)) ≤ RingHom.ker g ↔ (P.D₀.map g).mulVec (g ∘ v₀) = 0 := by
    rw [Ideal.span_le, Set.range_subset_iff, funext_iff]
    refine forall_congr' fun j => ?_
    rw [← RingHom.map_mulVec]
    rfl
  rw [hI]
  constructor
  · intro H
    obtain ⟨w, hw, hwu, -⟩ := loc_of_triv P h hM H
    obtain ⟨c, rfl⟩ := hker R' g w hw
    rw [Matrix.mulVec_smul] at hw
    exact ((unit_cst R' g X' π f' h c _ hwu).smul_eq_zero).1 hw
  · intro H
    refine triv_of_loc P h _ H fun y => ?_
    have hy : π y ∈ G := by
      by_contra hy
      refine hsub (a := f (π y)) ?_ ⟨π y, hy, rfl⟩
      change r₁ ∉ (f (π y)).asIdeal
      exact fun hm => (f (π y)).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hr₁')
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨i, ?_⟩
    rw [loc_comp P h, ← Scheme.preimage_basicOpen]
    exact hi

end GlobalTheory.UU.SecCyclic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAbelianPartDimAddTorusRank
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem HidaSetting.smoothDim_model : AllSet fun {_} _ _ _ {A} {G} _ _ _ => SmoothOfRelativeDimension A.g G.hom := by
  intro V _ _ _ A G _ _ s
  have hs : Smooth G.hom := s.semi.smooth
  have : GeometricallyConnected G.hom := s.semi.geomConnected
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group _ G).1
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have a := A.smoothDim
  have b : SmoothOfRelativeDimension (0 + A.g) ((Over.pullback (jK V)).obj G).hom := by
    have : IsIso s.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map s.gen.hom))
    rw [← Over.w s.gen.hom]; infer_instance
  have c : SmoothOfRelativeDimension n ((Over.pullback (jK V)).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hn
  have h₁ : n = A.g :=
    (H1.dim_unique _ c b (eSec _ (Classical.arbitrary (Spec (CommRingCat.of (FractionRing V)))))).trans (zero_add _)
  exact h₁ ▸ hn

theorem Tower.dim_eq_add_finrank : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (g' : ℕ), (SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X) ∧ ∀ a : t.Alg, SmoothOfRelativeDimension g' a.B.hom → A.g = g' + Module.finrank ℤ s.X := by
  intro V _ _ _ A G _ _ s t g'
  have hG : SmoothOfRelativeDimension A.g G.hom := HidaSetting.smoothDim_model V A G s
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by simpa using (IsLocalRing.maximalIdeal.isMaximal V).ne_top)
  have h₀ : SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X := fun h =>
    TQ.dim_eq_add_finrank _ s.X _ (t.l 0).Q A.g g'
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG) h
  refine ⟨h₀, fun a ha => h₀ ?_⟩
  obtain ⟨h, -⟩ := a.b_pb 0
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 ha

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndoEqOfSections
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.AutUniq

theorem hom_eq_of_sval {X X' Y B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (X ⟶ Y)} {ε : K → ℤ}
    {M : ℕ} (s : Fin (M + 1) → LB.Sec (LB.LinComb L φ ε)) (f : X ⟶ B) (p q : X' ⟶ X) (hf : p ≫ f = q ≫ f)
    (hcov : ⨆ i, nonzeroLocus (s i) = ⊤) (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (M + 1) → Γ(X, nonzeroLocus (s i))) (hr : ∀ i j, AmpleSpan.IsRatio (s j) (s i) (r i j))
    (hsurj : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom (r i)))
    (h : ∀ z : X', ∃ J, Good L z J ∧ ∃ u : (X'.presheaf.stalk z)ˣ, ∀ j, sval (s j) q z J = u.val * sval (s j) p z J) :
    p = q := by
  have mem : ∀ (χ : X' ⟶ X) i z J, Good L z J → (χ z ∈ nonzeroLocus (s i) ↔ IsUnit (sval (s i) χ z J)) :=
    fun χ i z J hJ => AmpleSpan.mem_nonzeroLocus_iff_gs (s i) χ z (hJ.mem φ χ)
  have rat : ∀ (χ : X' ⟶ X) i j z J, Good L z J → χ z ∈ nonzeroLocus (s i) →
      sval (s j) χ z J = gs χ z _ (r i j) * sval (s i) χ z J :=
    fun χ i j z J hJ hz => (hr i j).gs χ z hz (hJ.mem φ χ)
  have hm : ∀ i z, p z ∈ nonzeroLocus (s i) → q z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨J, hJ, u, hu⟩ := h z
    rw [mem q i z J hJ, hu]
    exact u.isUnit.mul ((mem p i z J hJ).1 hz)
  refine MapUniq.hom_ext_of_gs (fun i => nonzeroLocus (s i)) haff hcov p q hm fun i z hz a => ?_
  have hz' := hm i z hz
  obtain ⟨J, hJ, u, hu⟩ := h z
  have hrr : ∀ j, gs p z _ (r i j) = gs q z _ (r i j) := fun j => by
    have e := rat q i j z J hJ hz'
    rw [hu, hu, rat p i j z J hJ hz, mul_left_comm] at e
    have e' := (Units.mul_right_inj _).1 ((mul_left_comm _ _ _).trans e |>.trans (mul_left_comm _ _ _))
    exact ((mem p i z J hJ).1 hz).mul_right_cancel e'
  have cst : ∀ (χ : X' ⟶ X), χ z ∈ nonzeroLocus (s i) → ∀ c : Γ(B, ⊤),
      gs χ z _ ((f.appLE ⊤ (nonzeroLocus (s i)) le_top).hom c) = gs (χ ≫ f) z ⊤ c := fun χ hχ c =>
    (gs_res χ z le_top hχ _).trans (gs_pull χ f z ⊤ trivial _)
  obtain ⟨P, rfl⟩ := hsurj i a
  induction P using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, cst p hz, cst q hz', hf]
  | add P Q hP hQ => rw [map_add (f := _), gs_add p z _ hz, gs_add q z _ hz', hP, hQ]
  | mul_X P j hP => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul p z _ hz, gs_mul q z _ hz', hP, hrr]

theorem eq_of_twistPull {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hS : IsAffineOpen (⊤ : S.Opens)) {n : ℕ} (hV : VeryAmpleAt A L n) {T : Over S} (ψ ψ' : T ⊗ A ⟶ T ⊗ A)
    (h₁ : ψ ≫ fst _ _ = fst _ _) (h₂ : ψ' ≫ fst _ _ = fst _ _)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![(n : ℤ), -(n : ℤ)]))
    (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ' ≫ snd _ _).left] ![(n : ℤ), -(n : ℤ)]))
    (hα : α.IsGen) (hα' : α'.IsGen) (c : Γ(T.left, ⊤)ˣ)
    (H : ∀ t t₁ t₂ : LB.Sec (LPow A L n T), IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t t₁ →
      IsTwistPull A L ψ' (ψ' ≫ snd _ _) rfl n n α' t t₂ → ∀ j, t₂.f j = liftFun A _ c.val * t₁.f j) : ψ = ψ' := by
  obtain ⟨M, s, hcov, haff⟩ := hV ⊤ hS
  choose r hr hsurj using fun i => (haff i).2
  obtain ⟨i', hi⟩ : ∃ i' : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id⟩
  have sec : ∀ j, ∃ v : LB.Sec (LPow A L n T), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → VVRank.sv A v r z J =
        sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
          (r ≫ (snd T A).left ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ := fun _ : Fin n => (snd T A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => (n : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd T A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (VVRank.sval_pullTo _ _ _ r z hJ)⟩
  choose v hv using sec
  have key : ψ.left ≫ (snd T A).left ≫ i' = ψ'.left ≫ (snd T A).left ≫ i' := by
    refine hom_eq_of_sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s (A.hom ∣_ ⊤) _ _ ?_
      hcov (fun i => (haff i).1) r hr hsurj fun y => ?_
    · rw [← cancel_mono (⊤ : S.Opens).ι]
      simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hi, Over.w]
    · choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
      refine ⟨J, hJ, (val α' (𝟙 _) y J)⁻¹ * gm (𝟙 _ ≫ (fst T A).left) y ⊤ c * val α (𝟙 _) y J, fun j => ?_⟩
      obtain ⟨t₁, ht₁⟩ := VVRank.exists_isTwistPull A (hm := rfl) hL hα (v j)
      obtain ⟨t₂, ht₂⟩ := VVRank.exists_isTwistPull A (hm := rfl) hL hα' (v j)
      have e₁ := VVRank.sv_of_isTwistPull A ht₁ (𝟙 _) y hJ
      have e₂ := VVRank.sv_of_isTwistPull A ht₂ (𝟙 _) y hJ
      have hy := Good.mem hJ (fun _ : Fin 1 => (snd T A).left) (𝟙 (T ⊗ A).left)
      have e₃ : VVRank.sv A t₂ (𝟙 _) y J =
          (gm (𝟙 _ ≫ (fst T A).left) y ⊤ c).val * VVRank.sv A t₁ (𝟙 _) y J :=
        (congrArg (gs (𝟙 _) y _) (H _ _ _ ht₁ ht₂ _)).trans ((gs_mul _ y _ hy _ _).trans
          (congrArg (· * _) ((gs_res _ y le_top hy _).trans ((gs_pull _ _ y ⊤ trivial _).trans
            (gs_unit _ y ⊤ trivial c)))))
      rw [hv _ _ _ _ _ hJ, Category.id_comp] at e₁ e₂
      rw [Units.val_mul, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← e₁, ← e₃, e₂, Units.inv_mul_cancel_left]
  refine CartesianMonoidalCategory.hom_ext _ _ (h₁.trans h₂.symm) (Over.OverMorphism.ext ?_)
  have := congrArg (fun q => q ≫ (A.hom ⁻¹ᵁ ⊤).ι) key
  simpa only [Category.assoc, hi, Category.comp_id, Over.comp_left] using this

theorem endo_eq_of_sections : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ), 4 ≤ N → ∀ (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), ψ ≫ fst _ _ = fst _ _ → ψ' ≫ fst _ _ = fst _ _ → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (ψ ≫ snd _ _).left] ![(N : ℤ), -(N : ℤ)])) (α' : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (ψ' ≫ snd _ _).left] ![(N : ℤ), -(N : ℤ)])), α.IsGen → α'.IsGen → ∀ c : Γ((TFK (R := R) F).left, ⊤)ˣ, (∀ t t₁ t₂ : SecA A F N, IsTwistPull A.A A.L ψ (ψ ≫ snd _ _) rfl N N α t t₁ → IsTwistPull A.A A.L ψ' (ψ' ≫ snd _ _) rfl N N α' t t₂ → ∀ j, t₂.f j = liftFun A.A _ c.val * t₁.f j) → ψ = ψ' := by
  intro hL R _ _ A F _ _ N hN ψ ψ' h₁ h₂ α α' hα hα' c H
  exact eq_of_twistPull A.isLB (isAffineOpen_top _) (hL.1.ample _ A N hN).2 ψ ψ' h₁ h₂ α α' hα hα' c H

end GlobalTheory.AutUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfPowEqOneOfLocalHom
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem eq_one_of_pow_eq_one_of_localHom {W Ω : Type} [CommRing W] [IsLocalRing W] [Field Ω] (f : W →+* Ω)
    [IsLocalHom f] {N : ℕ} (hN : IsUnit (N : W)) {ζ : W} (h : ζ ^ N = 1) (hf : f ζ = 1) : ζ = 1 := by
  have hu : IsUnit (∑ i ∈ Finset.range N, ζ ^ i) := by
    refine isUnit_of_map_unit f _ ?_
    have := hN.map f
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, hf] using this
  have := geom_sum_mul ζ N
  rw [h, sub_self] at this
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 this)

theorem unit_eq_one_of_localHom {W Ω : Type} [CommRing W] [IsLocalRing W] [Field Ω] (f : W →+* Ω)
    [IsLocalHom f] {N : ℕ} (hN : IsUnit (N : W)) {ζ : Γ(Spec (CommRingCat.of W), ⊤)ˣ} (h : ζ ^ N = 1)
    (hf : Units.map (Spec.map (CommRingCat.ofHom f)).appTop.hom.toMonoidHom ζ = 1) : ζ = 1 := by
  have nat := congrArg (fun q => q.hom ζ.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  have hf' : (Spec.map (CommRingCat.ofHom f)).appTop.hom ζ.val = 1 := congrArg Units.val hf
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, hf', map_one, CommRingCat.hom_ofHom] at nat
  have h1 := eq_one_of_pow_eq_one_of_localHom f hN
    (ζ := (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom ζ.val)
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]) nat.symm
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact h1

theorem IsCPMap.cubWeil_iff {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {N : ℕ} {T : Over S'} {x y : T ⟶ G'} (hx : x ^ N = 1) (hy : y ^ N = 1)
    (ζ : Γ(T.left, ⊤)ˣ) : CubWeil P'.c N x y ζ ↔ CubWeil P.c N (toBase hw x) (toBase hw y) ζ := by
  refine ⟨cubWeil_map _ _ _ _ _ _ _ _ _ _ h N T x y ζ, fun h' => ?_⟩
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil P'.c hx hy
  have := (cubWeil_map _ _ _ _ _ _ _ _ _ _ h N T x y ξ hξ).unique h'
  exact this ▸ hξ

theorem TQ.Desc.cubWeil_one_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
    {Q : TQ G X} {P : CP G} (D : Q.Desc P) {N : ℕ} {T : Over S} {x y : T ⟶ G} (hx : x ^ N = 1) (hy : y ^ N = 1) :
    CubWeil P.c N x y 1 ↔ CubWeil D.M.c N (x ≫ Q.q) (y ≫ Q.q) 1 := by
  rw [D.map.cubWeil_iff hx hy]
  let ρ : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 T.left) (by simp)
  let ρ' : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have hw : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S := by simp
  have e : ∀ a : T ⟶ G, ρ ≫ toBase hw a = a ≫ Q.q := fun a =>
    Over.OverMorphism.ext (Category.id_comp (a.left ≫ Q.q.left))
  have e' : ∀ a : T ⟶ G, ρ' ≫ (a ≫ Q.q) = toBase hw a := fun a =>
    Over.OverMorphism.ext (Category.id_comp (a.left ≫ Q.q.left))
  constructor
  · intro h
    have := h.comp ρ
    rwa [e, e, map_one] at this
  · intro h
    have := h.comp ρ'
    rwa [e', e', map_one] at this

theorem cubWeil_one_iff_closedFibre : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (W Ω : Type) [CommRing W] [IsLocalRing W] [Algebra V W] [Field Ω] (f' : W →+* Ω), IsLocalHom f' → ∀ (p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1)))) (N : ℕ), IsUnit (N : V) → ∀ (y y' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (x x' : Over.mk p ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G), y ^ N = 1 → y' ^ N = 1 → x.left ≫ (fstG _ 0 G).left = (Spec.map (CommRingCat.ofHom f')) ≫ y.left → x'.left ≫ (fstG _ 0 G).left = (Spec.map (CommRingCat.ofHom f')) ≫ y'.left → (CubWeil s.P.c N y y' 1 ↔ CubWeil (t.l 0).D.M.c N (x ≫ (t.l 0).Q.q) (x' ≫ (t.l 0).Q.q) 1) := by
  intro V _ _ _ A G _ _ s t W Ω _ _ _ _ f' hf' p N hN y y' x x' hy hy' hx hx'
  let I := IsLocalRing.maximalIdeal V
  have hw : pullback.fst G.hom (thick V I 0) ≫ G.hom = (thickObj V I 0 G).hom ≫ thick V I 0 := pullback.condition
  obtain ⟨w, hl⟩ := (t.l 0).lev
  have hρ : Spec.map (CommRingCat.ofHom f') ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) =
      (Over.mk p).hom ≫ thick V I 0 := by
    have a := Over.w (toBase hw x)
    have b := Over.w y
    exact (congrArg (Spec.map (CommRingCat.ofHom f') ≫ ·) b).symm.trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) hx).symm.trans a))
  let ρ : Over.mk ((Over.mk p).hom ≫ thick V I 0) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom f')) hρ
  have e : ρ ≫ y = toBase hw x := Over.OverMorphism.ext hx.symm
  have e' : ρ ≫ y' = toBase hw x' := Over.OverMorphism.ext hx'.symm
  have inj : ∀ a b : Over.mk p ⟶ thickObj V I 0 G, toBase hw a = toBase hw b → a = b := fun a b h =>
    Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h) ((Over.w a).trans (Over.w b).symm))
  have tor : ∀ (a : Over.mk p ⟶ thickObj V I 0 G) (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G),
      b ^ N = 1 → ρ ≫ b = toBase hw a → a ^ N = 1 := fun a b hb h => by
    refine inj _ _ ((map_pow (toBaseHom hl.mul _) a N).trans (Eq.trans ?_ (map_one (toBaseHom hl.mul _)).symm))
    exact (congrArg (· ^ N) h.symm).trans (by rw [← MonObj.comp_pow, hb, MonObj.comp_one])
  have hxN := tor x y hy e
  have hxN' := tor x' y' hy' e'
  refine Iff.trans ?_ ((t.l 0).D.cubWeil_one_iff hxN hxN')
  refine Iff.trans ?_ (hl.cubWeil_iff hxN hxN' 1).symm
  constructor
  · intro h
    have := h.comp ρ
    rw [e, e', map_one] at this
    exact this
  · intro h
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil s.P.c hy hy'
    have c := hζ.comp ρ
    rw [e, e'] at c
    have hNW : IsUnit (N : W) := by simpa using hN.map (algebraMap V W)
    have : ζ = 1 := unit_eq_one_of_localHom f' hNW hζ.pow_eq_one (c.unique h)
    exact this ▸ hζ

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCoverOfIsProjByOfInfinite
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineCover

theorem exists_cover_of_isProjBy_of_infinite (K : Type) [Field K] [Infinite K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ) (hf : SmoothOfRelativeDimension g f) (hp : IsProjBy f) :
    ∃ D : Fin (g + 1) → X.Opens, (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨H, hH, m, s, hc, hs⟩ := hp
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := ⟨by
    have e : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hc]
      rfl
    rw [e]
    exact isCompact_iUnion fun i => (hs i).1.isCompact⟩
  have : IsNoetherian X := ⟨⟩
  obtain ⟨D, hD, h⟩ := exists_affine_le_coheight (X := X) (fun F hF =>
    exists_isAffineOpen_of_finite (cst f ⊤) hH s hc (fun i => (hs i).1) F hF) (g + 1)
  refine ⟨D, hD, top_le_iff.1 fun x _ => not_not.1 fun hx => ?_⟩
  have := (h x hx).trans (coheight_le_of_smooth f hf x)
  exact Nat.not_succ_le_self _ (by exact_mod_cast this)

theorem exists_cover_of_isProjBy :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → IsProjBy f → ∃ D : Fin (g + 1) → X.Opens, (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ :=
  fun K _ _ X _ f g hf hp => exists_cover_of_isProjBy_of_infinite K X f g hf hp

end GlobalTheory.AffineCover
end

