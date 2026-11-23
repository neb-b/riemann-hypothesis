module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GenericMap
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedFamilyBasisChange
section
open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange

theorem phiNormSq_baseChange : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (lab : Ψ → Ψ ⊕ Ψ) (r k m : ℕ) (h : r + k = m) (v : Fin r → V) (q : Ψ → Fin k → A.Λ) (bL : Ψ → Fin m → V) (T : Ψ → Matrix (Fin m) (Fin m) L), IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ)) → (∀ τ i, A.fam (lab τ) v (q τ) i = ∑ j, T τ j (Fin.cast h i) • bL τ j) → (∀ τ, (T τ).det ≠ 0) → ∀ (e : L →+* ℂ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) → Function.Injective j → ∀ (ρ' : 𝓞 E →+* Module.End ℂ V'), (∀ a x, ρ' a (j x) = j (A.ρ a x)) → (∀ τ a, eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a)) = j (eigComp A.ρ (A.σ (lab τ)) (v a))) → ∀ hb : V' → V' → ℂ, (∀ τ c c', hb (j (q τ c)) (j (q τ c')) = (A.Bq.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] A.f (q τ c)) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] A.f (q τ c'))) → PhiNormSq ρ' hb (A.I.map j) (4 * Real.pi)⁻¹ (fun τ => e.comp (A.σ (lab τ))) (fun τ i => j (bL τ i)) ((((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) * ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2) := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A lab r k m h v q bL T hv hq hfam hT e V' _ _ j hjs hji ρ' hρ' heig hb hhb
  classical
  obtain ⟨hvI, hvind, hvrel⟩ := hv
  have hsum : ∀ a : Fin r → 𝓞 E, ∑ i, ρ' (a i) (j (v i)) = j (∑ i, A.ρ (a i) (v i)) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hρ' _ _
  have hspan : oSpan ρ' (fun i => j (v i)) = (oSpan A.ρ v).map j := by
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.oSpan
    rw [AddMonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨a, i, rfl⟩
      exact ⟨A.ρ a (v i), ⟨a, i, rfl⟩, (hρ' a (v i)).symm⟩
    · rintro ⟨y, ⟨a, i, rfl⟩, rfl⟩
      exact ⟨a, i, (hρ' a (v i)).symm⟩
  have hrel : (oSpan ρ' (fun i => j (v i))).relIndex (A.I.map j) = (oSpan A.ρ v).relIndex A.I := by
    rw [hspan]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hji
  have hOF : IsOFamily ρ' (A.I.map j) (fun i => j (v i)) := by
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.IsOFamily
    refine ⟨fun i => AddSubgroup.mem_map_of_mem j (hvI i), fun a ha => hvind a (hji ?_), ?_⟩
    · rw [map_zero, ← hsum a]
      exact ha
    · rw [hrel]
      exact hvrel
  have hqe : ∀ τ c, j (q τ c) ∈ eigSp ρ' (e.comp (A.σ (lab τ))) := by
    intro τ c
    have hx0 := (hq τ).2 c
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.LinPt.eig at hx0
    rw [Submodule.mem_inf, Submodule.restrictScalars_mem] at hx0
    have hx := hx0.2
    simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    intro a
    rw [hρ', RingHom.comp_apply, ← hjs, ← map_sub, hx a, map_zero]
  have happ : ∀ τ i, Fin.append (fun a => eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a))) (fun c => j (q τ c)) i =
      ∑ j', (T τ).map e j' (Fin.cast h i) • j (bL τ j') := by
    intro τ i
    have hfi := hfam τ i
    have hap : Fin.append (fun a => eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a))) (fun c => j (q τ c)) i =
        j (A.fam (lab τ) v (q τ) i) := by
      unfold GlobalTheory.CompanionTheory.Ar.Cusp.LinPt.fam
      refine Fin.addCases (fun a => ?_) (fun c => ?_) i
      · simp only [Fin.append_left, heig]
      · simp only [Fin.append_right]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hap, hfi, map_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [hjs, Matrix.map_apply]
  have hdet : ∀ τ, ((T τ).map e).det = e (T τ).det := by
    intro τ
    rw [RingHom.map_det]
    rfl
  have hg : ∀ τ, (Matrix.of fun c c' => hb (j (q τ c)) (j (q τ c'))).det.re = A.gramDet e (q τ) := by
    intro τ
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.LinPt.gramDet
    congr 2
    ext c c'
    exact hhb τ c c'
  unfold GlobalTheory.CompanionTheory.Ar.Cusp.PhiNormSq
  refine ⟨r, k, h, fun i => j (v i), fun τ c => j (q τ c), fun τ => (T τ).map e, hOF, hqe, happ, ?_, ?_⟩
  · intro τ
    rw [hdet τ]
    exact (map_ne_zero e).mpr (hT τ)
  · rw [hrel]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hdet τ, hg τ]

end GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroCentreOfComplex
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem char_zero_centre_complex_point : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z), IsCptGen ξ → Char0 ξ ⟨centre z, h⟩ := by
  intro Ω _ X ξ z h _
  unfold Char0 InFibre unitAt regAt
  intro r hr hfib
  apply hfib
  have h1 := map_natCast (Scheme.stalkClosedPointTo z).hom r
  have h2 : IsUnit ((r : ℕ) : ℂ) := (Nat.cast_ne_zero.2 hr.ne_zero).isUnit
  rw [← h1] at h2
  obtain ⟨u, hu'⟩ := isUnit_of_map_unit _ _ h2
  have hv : genMap ξ ⟨centre z, h⟩ u.val = (r : Ω) :=
    (congrArg (genMap ξ ⟨centre z, h⟩) hu').trans (map_natCast _ r)
  refine ⟨?_, ⟨_, hv⟩, ⟨(u⁻¹).val, ?_⟩⟩
  · rw [← hv]
    exact (u.isUnit.map (genMap ξ ⟨centre z, h⟩)).ne_zero
  · exact (map_units_inv (genMap ξ ⟨centre z, h⟩) u).trans (congrArg Inv.inv hv)

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroIffNonzeroUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.CharTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ}

theorem unit_natCast (h : Char0 ξ q) (n : ℕ) (hn : n ≠ 0) : unitAt ξ q (n : Ω) :=
  _root_.UpperTheory.Reformulated.B.GenericMap.main h n hn

theorem char_zero_iff_integers_units (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [Algebra (𝓞 F) Ω]
    (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (t : κ → Ω) (ht : CoordTie (𝓞 F) ξ t) (p : Cpt ξ) :
    Char0 ξ p ↔ ∀ d : 𝓞 F, d ≠ 0 → unitAt ξ p (algebraMap (𝓞 F) Ω d) := by
  constructor
  · intro h d hd
    have hreg : ∀ b : 𝓞 F, algebraMap (𝓞 F) Ω b ∈ regAt ξ p := by
      intro b
      obtain ⟨c, hc⟩ := ht.cover p
      exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ b) p hc
    have hn : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hd
    obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {d}))
    have hu := unit_natCast h _ hn
    have e : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : Ω) = algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d' := by
      rw [← map_mul, ← hd', map_natCast]
    rw [e] at hu
    have ha : algebraMap (𝓞 F) Ω d ≠ 0 := left_ne_zero_of_mul hu.1
    have hb : algebraMap (𝓞 F) Ω d' ≠ 0 := right_ne_zero_of_mul hu.1
    refine ⟨ha, hreg d, ?_⟩
    have e2 : (algebraMap (𝓞 F) Ω d)⁻¹ =
        algebraMap (𝓞 F) Ω d' * (algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d')⁻¹ := by
      field_simp
    rw [e2]
    exact mul_mem (hreg d') hu.2.2
  · intro h r hr hf
    have hr0 : (r : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
    have := h _ hr0
    rw [map_natCast] at this
    exact hf this

end GlobalTheory.CompanionTheory.Ar.SncBase.CharTie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationTangentComb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
  {φ : G'.left ⟶ G.left}

theorem grpPull_mul (hφ : IsGrpPullback G' G f φ) (T : Over S') {g : T.left ⟶ S} (hg : g = T.hom ≫ f)
    (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hg
  exact hφ.2 T x y x₀ y₀ hx hy

theorem grpPull_one (hφ : IsGrpPullback G' G f φ) (T : Over S') {g : T.left ⟶ S} (hg : g = T.hom ≫ f) :
    (1 : Over.mk g ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  subst hg
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (1 : T ⟶ G'))
  let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have h := hφ.2 T 1 1 e e rfl rfl
  rw [_root_.mul_one] at h
  have h2 : e * e = e := Over.OverMorphism.ext h
  have h3 : e = 1 := mul_eq_left.1 h2
  exact (congrArg (fun q : Over.mk (T.hom ≫ f) ⟶ G => q.left) h3).symm

end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Same

variable {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}

theorem sameVec_one (Y : Model Xo c β) (y : Sp F ⟶ Xo.XF c) : SameVec Y y 1 1 := by
  let T : Over (Xo.XF c) := epsAt y
  refine ⟨(1 : T ⟶ Y.oF.t.G).left, Over.w _, ?_, ?_⟩
  · exact (grpPull_one Y.m0.cart T (Category.assoc _ _ _).symm).symm
  · exact (grpPull_one Y.m.cart T (Category.assoc _ _ _).symm).symm

theorem sameVec_mul {a b : epsAt (under y) ⟶ Xo.univ.t.G} {a' b' : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y a a') (h₂ : SameVec Y y b b') : SameVec Y y (a * b) (a' * b') := by
  obtain ⟨u₁, p₁, q₁, r₁⟩ := h₁
  obtain ⟨u₂, p₂, q₂, r₂⟩ := h₂
  let T : Over (Xo.XF c) := epsAt y
  let x₁ : T ⟶ Y.oF.t.G := Over.homMk u₁ p₁
  let x₂ : T ⟶ Y.oF.t.G := Over.homMk u₂ p₂
  refine ⟨(x₁ * x₂).left, Over.w (x₁ * x₂), ?_, ?_⟩
  · exact (grpPull_mul Y.m0.cart T (Category.assoc _ _ _).symm x₁ x₂ a b q₁.symm q₂.symm).symm
  · exact (grpPull_mul Y.m.cart T (Category.assoc _ _ _).symm x₁ x₂ a' b' r₁.symm r₂.symm).symm

theorem sameVec_scale {a u : epsAt (under y) ⟶ Xo.univ.t.G} {a' : epsAt (y ≫ Y.j) ⟶ Y.t.G} (h : SameVec Y y a a')
    (r : F) (hu : u.left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ a.left) :
    SameVec Y y u (LieTangent.epsScale (y ≫ Y.j) r ≫ a') := by
  obtain ⟨u₀, p, q, t⟩ := h
  refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ u₀, ?_, ?_, ?_⟩
  · rw [Category.assoc, p, ← Category.assoc, LieTangent.spec_eps_alg]
  · rw [Category.assoc, q, hu]
  · rw [Category.assoc, t]
    rfl

end Same

theorem valFam_sum {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {F : Type} [Field F]
    (y : Sp F ⟶ Xo.XF c) (hg : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) {n : ℕ} (e : Fin n → Z.V)
    (u : Fin n → (epsAt (under y) ⟶ Xo.univ.t.G))
    (h : ∀ j, ∃ a, Z.M.ValAt (y ≫ Y.j) (e j) a ∧ SameVec Y y (u j) a) :
    ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, e j) w' ∧ SameVec Y y (List.ofFn u).prod w' := by
  induction n with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · simpa using Z.M.valAt_zero hg
    · simpa using sameVec_one Y y
  | succ n ih =>
    obtain ⟨a, ha, hb⟩ := h 0
    obtain ⟨w', hw, hs⟩ := ih (fun i => e i.succ) (fun i => u i.succ) fun i => h i.succ
    refine ⟨a * w', ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      exact ha.add hw
    · rw [List.ofFn_succ, List.prod_cons]
      exact sameVec_mul hb hs

theorem valFam_sum_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (s : Fin n → Z.Ω) (r : Fin n → F) (w : epsAt (under y) ⟶ Xo.univ.t.G), genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → IsValFam Z y b v → (∀ j, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (s j) (r j)) → IsComb r v w → ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, s j • b j) w' ∧ SameVec Y y w w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F _ y n b v s r w hg h hs hw
  obtain ⟨u, hu, rfl⟩ := hw
  refine valFam_sum Z y hg _ u fun j => ?_
  obtain ⟨h1, t, e1, e2⟩ := hs j
  obtain ⟨a, ha, hb⟩ := h j
  have h2 := ha.smul h1 t
  rw [e1, e2] at h2
  exact ⟨_, h2, sameVec_scale hb (r j) (hu j)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordChartsMatchRegular
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.FracPts

variable {Ω : Type} [Field Ω]

theorem exists_prime_of_subset {k : Type} [CommRing k] [Algebra k Ω] (S : Subalgebra k Ω) (R : Subring Ω)
    (hR : IsLocalRing R) (h : ∀ s ∈ S, s ∈ R) :
    ∃ I : Ideal S, I.IsPrime ∧ ∀ s : S, s ∉ I ↔ ((s : Ω) ≠ 0 ∧ (s : Ω) ∈ R ∧ (s : Ω)⁻¹ ∈ R) := by
  let f : S →+* R := (S.val : S →+* Ω).codRestrict R (fun s => h s s.2)
  refine ⟨(IsLocalRing.maximalIdeal R).comap f, Ideal.IsPrime.comap f, fun s => ?_⟩
  have hs : (f s : Ω) = (s : Ω) := rfl
  rw [Ideal.mem_comap, IsLocalRing.notMem_maximalIdeal]
  constructor
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have h1 : ((u : R) : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have hu' : ((u : R) : Ω) = (s : Ω) := by rw [hu, hs]
    rw [hu'] at h1
    have h0 : (s : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨h0, h s s.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact (((u⁻¹ : Rˣ) : R)).2
  · rintro ⟨h0, h1, h2⟩
    refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, h2⟩ : R) (Subtype.ext ?_)
    change (s : Ω) * (s : Ω)⁻¹ = 1
    exact mul_inv_cancel₀ h0

variable {X : Scheme.{0}}

theorem mem_regAt_of_unitAt_mul {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} {s a : Ω} (hs : unitAt ξ p s)
    (h : s * a ∈ regAt ξ p) : a ∈ regAt ξ p := by
  have : a = s⁻¹ * (s * a) := by rw [inv_mul_cancel_left₀ hs.1]
  rw [this]
  exact (regAt ξ p).mul_mem hs.2.2 h

theorem unitAt_mul {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} {s a : Ω} (hs : unitAt ξ p s)
    (ha : unitAt ξ p a) : unitAt ξ p (s * a) := by
  refine ⟨mul_ne_zero hs.1 ha.1, (regAt ξ p).mul_mem hs.2.1 ha.2.1, ?_⟩
  rw [mul_inv]
  exact (regAt ξ p).mul_mem hs.2.2 ha.2.2

variable (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F]
  [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω]


include F in
theorem algebraMap_ne_zero {d : o} (hd : d ≠ 0) : algebraMap o Ω d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply o F Ω]
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd)

theorem adjoin_subset (S : Set Ω) : ∀ a ∈ Algebra.adjoin o S, a ∈ Algebra.adjoin F S := by
  have : Algebra.adjoin o S ≤ (Algebra.adjoin F S).restrictScalars o :=
    Algebra.adjoin_le Algebra.subset_adjoin
  exact fun a ha => this ha

theorem exists_mul_mem_adjoin (S : Set Ω) (b : Ω) (hb : b ∈ Algebra.adjoin F S) :
    ∃ d : o, d ≠ 0 ∧ algebraMap o Ω d * b ∈ Algebra.adjoin o S := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := o) r
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨d, hd0, ?_⟩
    have hF : algebraMap o F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd0
    have : algebraMap o Ω d * algebraMap F Ω (algebraMap o F n / algebraMap o F d) = algebraMap o Ω n := by
      rw [IsScalarTower.algebraMap_apply o F Ω d, ← map_mul, mul_div_cancel₀ _ hF,
        ← IsScalarTower.algebraMap_apply]
    rw [this]
    exact Subalgebra.algebraMap_mem _ n
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have : algebraMap o Ω (d * e) * (x + y) =
        algebraMap o Ω e * (algebraMap o Ω d * x) + algebraMap o Ω d * (algebraMap o Ω e * y) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ e) h) (mul_mem (Subalgebra.algebraMap_mem _ d) h')
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have : algebraMap o Ω (d * e) * (x * y) = (algebraMap o Ω d * x) * (algebraMap o Ω e * y) := by
      rw [map_mul]; ring
    rw [this]
    exact mul_mem h h'

variable {W : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ W}
  {κ : Type} {t : κ → Ω}

theorem unitAt_algebraMap (hF : CoordTie F ξ' t) {c : κ} {p' : Cpt ξ'} (hc : InChart ξ' t c p') {d : o}
    (hd : d ≠ 0) : unitAt ξ' p' (algebraMap o Ω d) := by
  have hF0 : algebraMap o F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd
  have hmem : ∀ r : F, algebraMap F Ω r ∈ regAt ξ' p' := fun r =>
    (hF.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ r) p' hc
  refine ⟨algebraMap_ne_zero o F hd, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_apply o F Ω]
    exact hmem _
  · rw [IsScalarTower.algebraMap_apply o F Ω, ← map_inv₀]
    exact hmem _

theorem regAt_eq_of_units (hA : CoordTie o ξ t) (hF : CoordTie F ξ' t) {c : κ} {p : Cpt ξ} {p' : Cpt ξ'}
    (hc : InChart ξ t c p) (hc' : InChart ξ' t c p')
    (hu : ∀ s ∈ Algebra.adjoin o (Set.range fun j => t j / t c), unitAt ξ p s ↔ unitAt ξ' p' s) :
    regAt ξ p = regAt ξ' p' := by
  have hB : ∀ b ∈ Algebra.adjoin F (Set.range fun j => t j / t c), b ∈ regAt ξ' p' := fun b hb =>
    (hF.ring c hc'.1 b).1 hb p' hc'
  have hA' : ∀ b ∈ Algebra.adjoin o (Set.range fun j => t j / t c), b ∈ regAt ξ' p' := fun b hb =>
    hB b (adjoin_subset o F _ b hb)
  have hAp : ∀ b ∈ Algebra.adjoin o (Set.range fun j => t j / t c), b ∈ regAt ξ p := fun b hb =>
    (hA.ring c hc.1 b).1 hb p hc
  ext a
  constructor
  · intro ha
    obtain ⟨s, hs, hsu, hsa⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ o κ t hA c p hc a).1 ha
    exact mem_regAt_of_unitAt_mul ((hu s hs).1 hsu) (hA' _ hsa)
  · intro ha
    obtain ⟨s, hs, hsu, hsa⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction W Ω ξ' F κ t hF c p' hc' a).1 ha
    obtain ⟨d, hd, hds⟩ := exists_mul_mem_adjoin o F _ s hs
    obtain ⟨e, he, hes⟩ := exists_mul_mem_adjoin o F _ _ hsa
    have hunit : unitAt ξ' p' (algebraMap o Ω e * (algebraMap o Ω d * s)) :=
      unitAt_mul (unitAt_algebraMap o F hF hc' he) (unitAt_mul (unitAt_algebraMap o F hF hc' hd) hsu)
    have hmemA : algebraMap o Ω e * (algebraMap o Ω d * s) ∈
        Algebra.adjoin o (Set.range fun j => t j / t c) :=
      mul_mem (Subalgebra.algebraMap_mem _ e) hds
    refine (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ o κ t hA c p hc a).2
      ⟨_, hmemA, (hu _ hmemA).2 hunit, ?_⟩
    have : algebraMap o Ω e * (algebraMap o Ω d * s) * a =
        algebraMap o Ω d * (algebraMap o Ω e * (s * a)) := by ring
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ d) hes

theorem regAt_frac :
    ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type) [Field Ω]
      [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (X W : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ W) (κ : Type)
      (t : κ → Ω), CoordTie o ξ t → CoordTie F ξ' t →
      (∀ p' : Cpt ξ', ∃ p : Cpt ξ, regAt ξ p = regAt ξ' p') ∧
        ∀ p : Cpt ξ, (∀ d : o, d ≠ 0 → unitAt ξ p (algebraMap o Ω d)) → ∃ p' : Cpt ξ', regAt ξ p = regAt ξ' p' := by
  intro o F _ _ _ _ _ Ω _ _ _ _ X W ξ ξ' κ t hA hF
  constructor
  · intro p'
    obtain ⟨c, hc⟩ := hF.cover p'
    have hloc : IsLocalRing (regAt ξ' p') := (regAt_isLocalRing_isFractionRing_stalk W Ω ξ' hF.gen p').1
    have hsub : ∀ s ∈ Algebra.adjoin o (Set.range fun j => t j / t c), s ∈ regAt ξ' p' := fun s hs =>
      (hF.ring c hc.1 s).1 (adjoin_subset o F _ s hs) p' hc
    obtain ⟨I, hI, hIu⟩ := exists_prime_of_subset _ (regAt ξ' p') hloc hsub
    obtain ⟨p, ⟨hp, hpu⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.chart_point_of_prime X Ω ξ o κ t hA c hc.1 I hI
    refine ⟨p, regAt_eq_of_units o F hA hF hp hc fun s hs => ?_⟩
    exact (hpu ⟨s, hs⟩).symm.trans (hIu ⟨s, hs⟩)
  · intro p hd
    obtain ⟨c, hc⟩ := hA.cover p
    have hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hA.gen p).1
    have hsub : ∀ s ∈ Algebra.adjoin F (Set.range fun j => t j / t c), s ∈ regAt ξ p := fun s hs => by
      obtain ⟨d, hd0, hds⟩ := exists_mul_mem_adjoin o F _ s hs
      exact mem_regAt_of_unitAt_mul (hd d hd0) ((hA.ring c hc.1 _).1 hds p hc)
    obtain ⟨I, hI, hIu⟩ := exists_prime_of_subset _ (regAt ξ p) hloc hsub
    obtain ⟨p', ⟨hp', hpu⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.chart_point_of_prime W Ω ξ' F κ t hF c hc.1 I hI
    refine ⟨p', regAt_eq_of_units o F hA hF hc hp' fun s hs => ?_⟩
    have hsB := adjoin_subset o F _ s hs
    exact (hIu ⟨s, hsB⟩).symm.trans (hpu ⟨s, hsB⟩)

end GlobalTheory.CompanionTheory.Ar.SncBase.FracPts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EveryComponentInSomeChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_inChart_of_comp_eq :
    ∀ (W P : Scheme.{0}) (Ω : Type) [Field Ω] (ξ' : Sp Ω ⟶ W) (ξ₀ : Sp Ω ⟶ P) (g : W ⟶ P) (o : Type) [CommRing o]
      [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → ξ' ≫ g = ξ₀ → ∀ p' : Cpt ξ', ∃ c, InChart ξ' u c p' := by
  intro W P Ω _ ξ' ξ₀ g o _ _ κ u h he p'
  have hd : Dominates ξ' ξ₀ g (RingHom.id Ω) := by
    have e : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 (Spec (CommRingCat.of Ω)) := by
      exact Spec.map_id _
    show ξ' ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ₀
    rw [e, Category.id_comp]
    exact he
  obtain ⟨hs, hreg, -⟩ := RegAtDom.regAt_dominates P Ω ξ₀ W Ω ξ' g (RingHom.id Ω) hd p'
  obtain ⟨c, hc, hr⟩ := h.cover ⟨g p'.1, hs⟩
  exact ⟨c, hc, fun c' => hreg _ (hr c')⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
end

