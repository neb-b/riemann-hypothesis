module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SchemeImage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0119

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalZeroOfMemHomogeneousIdeal
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoVanish

open HomogeneousLocalization MvPolynomial

variable {K : Type} [Field K] {N : ℕ}

theorem away_mk_zero {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) (n : ℕ)
    (h0 : (0 : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n 0 h0 = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]

theorem away_mk_add {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) (n : ℕ)
    {a b : MvPolynomial (Fin (N + 1)) K} (ha : a ∈ grK K N (n • 1)) (hb : b ∈ grK K N (n • 1))
    (hab : a + b ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n (a + b) hab = Away.mk (grK K N) hx n a ha + Away.mk (grK K N) hx n b hb := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_add, Localization.add_mk_self]

theorem away_mk_mul {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) {k m n : ℕ} (hn : k + m = n)
    {a b : MvPolynomial (Fin (N + 1)) K} (ha : a ∈ grK K N (k • 1)) (hb : b ∈ grK K N (m • 1))
    (hab : a * b ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n (a * b) hab = Away.mk (grK K N) hx k a ha * Away.mk (grK K N) hx m b hb := by
  subst hn
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add x k m)

theorem chart_zero {R : Type} [CommRing R] {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1)
    (φ : Away (grK K N) x →+* R) (S : Set (MvPolynomial (Fin (N + 1)) K))
    (hS : ∀ f ∈ S, ∃ (d : ℕ) (hf : f ∈ grK K N (d • 1)), φ (Away.mk (grK K N) hx d f hf) = 0)
    {p : MvPolynomial (Fin (N + 1)) K} (hp : p ∈ Ideal.span S) :
    ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
      f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) →
        φ (Away.mk (grK K N) hx n f hf) = 0 := by
  have hmem : ∀ (q : MvPolynomial (Fin (N + 1)) K) (n : ℕ),
      (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1) := by
    intro q n
    simpa using (DirectSum.decompose (grK K N) q n).2
  have hzero : ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
      f = (DirectSum.decompose (grK K N) (0 : MvPolynomial (Fin (N + 1)) K) n : MvPolynomial (Fin (N + 1)) K) →
        φ (Away.mk (grK K N) hx n f hf) = 0 := by
    intro n f hf h
    have h0 : f = 0 := by simpa using h
    subst h0
    rw [away_mk_zero, map_zero]
  have hadd : ∀ (p q : MvPolynomial (Fin (N + 1)) K),
      (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0) →
      (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0) →
      ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) (p + q) n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0 := by
    intro p q ihp ihq n f hf h
    have h' : f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) +
        (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) := by
      rw [h, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
    subst h'
    rw [away_mk_add hx n (hmem p n) (hmem q n), map_add (f := _), ihp n _ _ rfl, ihq n _ _ rfl, add_zero]
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨d, hd, h0⟩ := hS p hp
    intro n f hf h
    have hd' : p ∈ grK K N d := by simpa using hd
    by_cases hnd : n = d
    · subst hnd
      have : f = p := h.trans (DirectSum.decompose_of_mem_same _ hd')
      subst this
      exact h0
    · have h1 : f = 0 := h.trans (DirectSum.decompose_of_mem_ne _ hd' (Ne.symm hnd))
      subst h1
      rw [away_mk_zero, map_zero]
  | zero => exact hzero
  | add p q _ _ ihp ihq => exact hadd p q ihp ihq
  | smul a p _ ih =>
    induction a using DirectSum.Decomposition.inductionOn (grK K N) with
    | zero => simpa using hzero
    | @homogeneous k m =>
      intro n f hf h
      rw [smul_eq_mul] at h
      by_cases hk : k ≤ n
      · rw [DirectSum.coe_decompose_mul_of_left_mem_of_le _ m.2 hk] at h
        subst h
        have hm1 : (m : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (k • 1) := by simpa using m.2
        rw [away_mk_mul hx (by omega : k + (n - k) = n) hm1 (hmem p (n - k)), map_mul,
          ih (n - k) _ _ rfl, mul_zero]
      · rw [DirectSum.coe_decompose_mul_of_left_mem_of_not_le _ m.2 hk] at h
        subst h
        rw [away_mk_zero, map_zero]
    | add a b iha ihb =>
      rw [add_smul]
      exact hadd _ _ iha ihb

theorem evV_res {X : Scheme.{0}} (i : X ⟶ PSpace K N) (g : MvPolynomial (Fin (N + 1)) K) {V W : X.Opens}
    (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (h : W ≤ V) (y : Away (grK K N) g) :
    resO h (evV i g V hV y) = evV i g W (h.trans hV) y := by
  have := Scheme.Hom.appLE_map i hV (homOfLE h).op
  simp only [evV]
  exact congr($(this).hom ((Proj.awayToSection (grK K N) g).hom y))

theorem evV_awayMap {X : Scheme.{0}} (i : X ⟶ PSpace K N) {a b c : MvPolynomial (Fin (N + 1)) K} {m : ℕ}
    (hb : b ∈ grK K N m) (hc : c = a * b) {W : X.Opens} (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) c)
    (hW' : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) a) (y : Away (grK K N) a) :
    evV i c W hW (awayMap (grK K N) hb hc y) = evV i a W hW' y := by
  have h1 := Proj.awayMap_awayToSection (grK K N) hb hc
  have h2 := Scheme.Hom.map_appLE i hW (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op
  have h3 : (Proj.awayToSection (grK K N) c).hom (awayMap (grK K N) hb hc y) =
      ((PSpace K N).presheaf.map (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op).hom
        ((Proj.awayToSection (grK K N) a).hom y) := congr($(h1).hom y)
  simp only [evV, RingHom.comp_apply]
  rw [h3]
  exact congr($(h2).hom ((Proj.awayToSection (grK K N) a).hom y))

theorem exists_chart (p : PSpace K N) : ∃ j, p ∈ Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) := by
  have h : ⨆ j, Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) = ⊤ := by
    refine Proj.iSup_basicOpen_eq_top _ _ ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun n hn f hf => ?_)
    change f ∈ Ideal.span _
    rw [← Set.image_univ, mem_ideal_span_X_image]
    intro m hm
    by_contra! H
    obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
    have hf' : f ∈ grK K N n := hf
    have := ((mem_homogeneousSubmodule _ _).1 hf') (mem_support_iff.1 hm)
    simp only [map_zero] at this
    omega
  exact TopologicalSpace.Opens.mem_iSup.1 (h.ge (Set.mem_univ p))

theorem ratio_eq {g x f : MvPolynomial (Fin (N + 1)) K} {e s : ℕ} (hg : g ∈ grK K N e) (hx : x ∈ grK K N 1)
    (hf : f ∈ grK K N (s • e)) (hf1 : f ∈ grK K N ((s • e) • 1)) (hxs : x ^ (s • e) ∈ grK K N (s • e)) :
    awayMap (grK K N) hx (rfl : g * x = g * x) (Away.mk (grK K N) hg s f hf) =
      awayMap (grK K N) hx (rfl : g * x = g * x) (Away.mk (grK K N) hg s (x ^ (s • e)) hxs) *
        awayMap (grK K N) hg (mul_comm g x) (Away.mk (grK K N) hx (s • e) f hf1) := by
  apply HomogeneousLocalization.val_injective
  simp only [awayMap_mk, Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.GeoVanish


open GlobalTheory.CompanionTheory.GeoVanish in
theorem GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e) (hg : g ∈ grK K N e) {s : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (s • e)), f ∈ homIdeal i → ∀ (V : X.Opens) (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g), evV i g V hV (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0 := by
  intro K _ X N i g e he hg s f hf hfI V hV
  have hf1 : f ∈ grK K N ((s • e) • 1) := by simpa using hf
  have key : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) (s • e) f hf1) = 0 := by
    intro j
    refine chart_zero (xv_mem K N j) (evV i (MvPolynomial.X j) _ le_rfl) _ ?_ hfI (s • e) f hf1
      (DirectSum.decompose_of_mem_same _ hf).symm
    rintro p ⟨d, hp, h⟩
    exact ⟨d, hp, h j⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun j : Fin (N + 1) => V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) V
    (fun j => homOfLE inf_le_left) ?_ _ _ ?_
  · intro p hp
    obtain ⟨j, hj⟩ := exists_chart (i p)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
    exact And.intro hp hj
  · intro j
    set x : MvPolynomial (Fin (N + 1)) K := MvPolynomial.X j with hxdef
    have hx : x ∈ grK K N 1 := xv_mem K N j
    set W := V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) x with hWdef
    have hWg : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g := inf_le_left.trans hV
    have hWx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x := inf_le_right
    have hWgx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (g * x) := by
      rw [Proj.basicOpen_mul]
      exact fun p hp => And.intro (hWg hp) (hWx hp)
    have hxs : x ^ (s • e) ∈ grK K N (s • e) := by
      simpa using SetLike.pow_mem_graded (s • e) hx
    have h0 : evV i x W hWx (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) f hf1) = 0 := by
      rw [← evV_res i x le_rfl hWx, key j, map_zero]
    have h1 : evV i g W hWg (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0 := by
      rw [← evV_awayMap i hx rfl hWgx hWg, ratio_eq hg hx hf hf1 hxs, map_mul,
        evV_awayMap i hg (mul_comm g x) hWgx hWx, h0, mul_zero]
    change resO (inf_le_left : W ≤ V) (evV i g V hV _) = resO (inf_le_left : W ≤ V) 0
    rw [map_zero, evV_res i g hV inf_le_left]
    exact h1
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSubfieldModel
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace GlobalTheory.CompanionTheory.FieldModel

theorem exists_subfield_model : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField K) (_ : IsAlgClosure K (AlgebraicClosure ℚ)) (e : F ≃+* K) (E : Ω ≃+* (AlgebraicClosure ℚ)), ∀ x : F, E (algebraMap F Ω x) = algebraMap K (AlgebraicClosure ℚ) (e x) := by
  intro F Ω _ _ _ _ _
  let σ : F →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : F ≃ₐ[ℚ] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  haveI fd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional
  haveI nf : NumberField σ.fieldRange := { to_charZero := inferInstance, to_finiteDimensional := fd }
  haveI alg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      (AlgebraicClosure.isAlgebraic ℚ)
    convert h
  haveI ac : IsAlgClosure σ.fieldRange (AlgebraicClosure ℚ) :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) σ.fieldRange⟩
  refine ⟨σ.fieldRange, nf, ac, e.toRingEquiv, IsAlgClosure.equivOfEquiv Ω (AlgebraicClosure ℚ) e.toRingEquiv, fun x => ?_⟩
  exact IsAlgClosure.equivOfEquiv_algebraMap Ω (AlgebraicClosure ℚ) e.toRingEquiv x

end GlobalTheory.CompanionTheory.FieldModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendedFormNaturality
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.OneFormCoh

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def extForm (hp : Par F) (l : Glob1 F →ₗ[R] R) (T : C) : Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T :=
  (hp T).lift ((Algebra.linearMap R (F.obj T)) ∘ₗ l)

theorem extForm_ev (hp : Par F) (l : Glob1 F →ₗ[R] R) (T : C) (v : Glob1 F) :
    extForm F hp l T (v.1 T) = algebraMap R (F.obj T) (l v) :=
  (hp T).lift_eq _ v

theorem extended_form_naturality (hp : Par F) (l : Glob1 F →ₗ[R] R) {T T' : C} (φ : T ⟶ T') (α : Ω[F.obj T⁄R]) :
    extForm F hp l T' (p1 F φ α) = mp F φ (extForm F hp l T α) := by
  refine (hp T).inductionOn α ?_ ?_ ?_
  · intro v
    change GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T' (GlobalTheory.CechDR.p1 F φ (v.1 T)) =
      GlobalTheory.CatCoh.mp F φ (GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T (v.1 T))
    have hv : GlobalTheory.CechDR.p1 F φ (v.1 T) = v.1 T' := by
      first
        | exact v.2 φ
        | exact v.2 T T' φ
        | exact (v.2 φ).symm
        | exact (v.2 T T' φ).symm
    rw [hv, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, AlgHom.commutes]
  · intro s n hn
    rw [GlobalTheory.CechDR.oneFormsMapOfFunctorMorphism_smul, map_smul, map_smul, hn, smul_eq_mul, smul_eq_mul, map_mul]
  · intro n₁ n₂ h₁ h₂
    rw [map_add (f := _), map_add (f := _), h₁, h₂, map_add (f := _), map_add (f := _)]

theorem extForm_sum (hp : Par F) {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Glob1 F →ₗ[R] R)
    (hw : ∀ v, ∑ i, l i v • w i = v) (T : C) (α : Ω[F.obj T⁄R]) :
    ∑ i, extForm F hp (l i) T α • (w i).1 T = α := by
  refine (hp T).inductionOn α ?_ ?_ ?_
  · intro v
    change ∑ i, GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp (l i) T (v.1 T) • (w i).1 T = v.1 T
    simp only [GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, algebraMap_smul]
    have h := congrArg (MainStatements.Hodge.evForm F T) (hw v)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_smul] at h
    exact h
  · intro s m hm
    conv_rhs => rw [← hm]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_smul]
  · intro m₁ m₂ h₁ h₂
    conv_rhs => rw [← h₁, ← h₂]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add (f := _), add_smul]

def muMap : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F :=
  TensorProduct.lift (LinearMap.mk₂ R (fun (f : Z1 F) (v : Glob1 F) T T' φ ↦ f.1 T T' φ • v.1 T')
    (fun f f' v ↦ by funext T T' φ; simp [add_smul])
    (fun r f v ↦ by funext T T' φ; simp)
    (fun f v v' ↦ by funext T T' φ; simp)
    (fun r f v ↦ by funext T T' φ; simp [smul_comm r]))

theorem muMap_tmul (f : Z1 F) (v : Glob1 F) {T T' : C} (φ : T ⟶ T') :
    muMap F (f ⊗ₜ v) T T' φ = f.1 T T' φ • v.1 T' := rfl

def contr (l : Glob1 F →ₗ[R] R) : Z1 F ⊗[R] Glob1 F →ₗ[R] Z1 F :=
  (TensorProduct.rid R (Z1 F)).toLinearMap ∘ₗ LinearMap.lTensor (Z1 F) l

theorem contr_tmul (l : Glob1 F →ₗ[R] R) (f : Z1 F) (v : Glob1 F) :
    contr F l (f ⊗ₜ v) = l v • f := by
  simp [contr]

theorem extForm_muMap (hp : Par F) (l : Glob1 F →ₗ[R] R) (t : Z1 F ⊗[R] Glob1 F) {T T' : C}
    (φ : T ⟶ T') : extForm F hp l T' (muMap F t T T' φ) = (contr F l t).1 T T' φ := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact map_zero _
  | add x y hx hy =>
    simp only [map_add (f := _), Pi.add_apply, Submodule.coe_add, hx, hy]
  | tmul f v =>
    simp only [GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul, GlobalTheory.CompanionTheory.OneFormCoh.contr_tmul, map_smul, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
    ring

theorem sum_contr {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Glob1 F →ₗ[R] R)
    (hw : ∀ v, ∑ i, l i v • w i = v) (t : Z1 F ⊗[R] Glob1 F) :
    ∑ i, contr F (l i) t ⊗ₜ[R] w i = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]
  | tmul f v =>
    simp_rw [GlobalTheory.CompanionTheory.OneFormCoh.contr_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, hw]

def pushZ (hp : Par F) (l : Glob1 F →ₗ[R] R) (a : A1 F)
    (ha : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) : Z1 F :=
  ⟨fun T T' φ ↦ extForm F hp l T' (a T T' φ), fun T T' T'' φ ψ ↦ by
    change extForm F hp l T'' (a T T'' (φ ≫ ψ)) =
      mp F ψ (extForm F hp l T' (a T T' φ)) + extForm F hp l T'' (a T' T'' ψ)
    rw [ha, map_add (f := _), extended_form_naturality]⟩

theorem main (hF : Framed F) :
    ∃ mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F, (∀ f ω T T' φ, mu (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T') ∧
      (∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
        a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, mu t = a) ∧
      ∀ (t : Z1 F ⊗[R] Glob1 F) (β : A0 F), (∀ T T' φ, mu t T T' φ = β T' - p1 F φ (β T)) →
        (H1.mk F).rTensor (Glob1 F) t = 0 := by
  obtain ⟨-, hp, hfin, hproj⟩ := hF
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R (GlobalTheory.CechDR.Glob1 F)
  obtain ⟨w, l, hw⟩ : ∃ (w : Fin n → GlobalTheory.CechDR.Glob1 F) (l : Fin n → GlobalTheory.CechDR.Glob1 F →ₗ[R] R),
      ∀ v, ∑ i, l i v • w i = v := by
    refine ⟨fun i => f (Pi.single i 1), fun i => LinearMap.proj i ∘ₗ g, fun v => ?_⟩
    have hsum : ∑ i, g v i • (Pi.single i 1 : Fin n → R) = g v := by
      ext j
      simp [Pi.single_apply]
    calc ∑ i, (LinearMap.proj i ∘ₗ g) v • f (Pi.single i 1)
        = f (∑ i, g v i • (Pi.single i 1 : Fin n → R)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          simp only [map_smul, LinearMap.comp_apply, LinearMap.proj_apply]
      _ = v := by
          rw [hsum]
          exact LinearMap.congr_fun hfg v
  refine ⟨GlobalTheory.CompanionTheory.OneFormCoh.muMap F, fun x ω T T' φ => GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul F x ω φ, ?_, ?_⟩
  · intro a ha
    refine ⟨∑ i, GlobalTheory.CompanionTheory.OneFormCoh.pushZ F hp (l i) a ha ⊗ₜ w i, ?_⟩
    funext T T' φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [Finset.sum_apply, GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul]
    exact GlobalTheory.CompanionTheory.OneFormCoh.extForm_sum F hp w l hw T' (a T T' φ)
  · intro t β hβ
    have hzero : ∀ i, GlobalTheory.CatCoh.H1.mk F
        (GlobalTheory.CompanionTheory.OneFormCoh.contr F (l i) t) = 0 := by
      intro i
      rw [GlobalTheory.CatCoh.H1.mk_eq_zero]
      refine ⟨fun T => GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp (l i) T (β T), ?_⟩
      funext T T' φ
      rw [GlobalTheory.CatCoh.amitsur_d0_apply, ← GlobalTheory.CompanionTheory.OneFormCoh.extForm_muMap F hp, hβ, map_sub,
        GlobalTheory.CompanionTheory.OneFormCoh.extended_form_naturality]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← GlobalTheory.CompanionTheory.OneFormCoh.sum_contr F w l hw t, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.rTensor_tmul, hzero, TensorProduct.zero_tmul]

theorem oneFormCohSt : OneFormCohSt := by
  unfold MainStatements.Hodge.OneFormCohSt MainStatements.Hodge.AllF
  intro R _ C _ F hF
  exact GlobalTheory.CompanionTheory.OneFormCoh.main F hF

end GlobalTheory.CompanionTheory.OneFormCoh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClass
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SerreFin

theorem finite_mid {R : Type} [CommRing R] [IsNoetherianRing R] {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : Function.Exact f g)
    [Module.Finite R M₁] [Module.Finite R M₃] : Module.Finite R M₂ := by
  have hk : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.1 h
  haveI : Module.Finite R (LinearMap.ker g) := by
    rw [hk]
    exact Module.Finite.range f
  haveI : IsNoetherian R M₃ := isNoetherian_of_isNoetherianRing_of_finite R M₃
  haveI : Module.Finite R (M₂ ⧸ LinearMap.ker g) := Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

theorem exists_serre_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∃ 𝒮 : Serre.{1} R,
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ Module.Finite R M := by
  intro R _ _
  refine ⟨⟨fun M _ _ => Module.Finite R M, fun M _ _ _ => ?_, ?_⟩, fun M _ _ => Iff.rfl⟩
  · exact Module.Finite.of_surjective (0 : (Fin 0 → R) →ₗ[R] M)
      (fun x => ⟨0, Subsingleton.elim _ _⟩)
  · intro M₁ M₂ M₃ _ _ _ _ _ _ f g h h₁ h₃
    exact finite_mid f g h

end GlobalTheory.CompanionTheory.SerreFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismUniqueness
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.FormalUniq

theorem eq_of_comp_thickenings_eq :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) →
    ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  intro R _ _ I hI X Z hX hZ Y b hpb g g' hb
  have hw : g.left ≫ Z.hom = g'.left ≫ Z.hom := by rw [Over.w g, Over.w g']
  obtain ⟨L, hL1, hL2⟩ : ∃ L : X.left ⟶ pullback Z.hom Z.hom,
      L ≫ pullback.fst _ _ = g.left ∧ L ≫ pullback.snd _ _ = g'.left :=
    ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hfac : ∀ e : ℕ, ∃ h, h ≫ pullback.snd (pullback.diagonal Z.hom) L =
      pullback.fst X.hom (thick R I e) := by
    intro e
    have hfe : pullback.fst X.hom (thick R I e) ≫ g.left =
        pullback.fst X.hom (thick R I e) ≫ g'.left := by
      rw [← (hpb e).isoPullback_inv_fst, Category.assoc, Category.assoc, hb e]
    refine ⟨pullback.lift (pullback.fst X.hom (thick R I e) ≫ g.left)
      (pullback.fst X.hom (thick R I e)) ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, hL1]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, hL2, hfe]
  haveI : IsIso (pullback.snd (pullback.diagonal Z.hom) L) :=
    GlobalTheory.CompanionTheory.FormalClosed.isIso_of_isClosedImmersion_of_thickenings R I hI X hX _ _ inferInstance hfac
  have hc := pullback.condition (f := pullback.diagonal Z.hom) (g := L)
  have e1 := congrArg (· ≫ pullback.fst Z.hom Z.hom) hc
  have e2 := congrArg (· ≫ pullback.snd Z.hom Z.hom) hc
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    hL1, hL2] at e1 e2
  exact Over.OverMorphism.ext
    ((cancel_epi (pullback.snd (pullback.diagonal Z.hom) L)).mp (e1.symm.trans e2))

end GlobalTheory.CompanionTheory.FormalUniq
end

