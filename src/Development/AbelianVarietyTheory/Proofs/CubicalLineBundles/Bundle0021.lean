module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAl
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem abelianScheme_hom_extends_dedekind_of_isGrpPullback :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (G₀ G₀' : Over (Sp K)) [GrpObj G₀] [GrpObj G₀'] (φ : G₀.left ⟶ G.left) (φ' : G₀'.left ⟶ G'.left), IsAbelianScheme G → IsAbelianScheme G' → IsGrpPullback G₀ G (spMap (algebraMap R K)) φ → IsGrpPullback G₀' G' (spMap (algebraMap R K)) φ' → ∀ f : G₀ ⟶ G₀', IsMonHom f → ∃ F : G ⟶ G', IsMonHom F ∧ f.left ≫ φ' = φ ≫ F.left ∧ ∀ F' : G ⟶ G', f.left ≫ φ' = φ ≫ F'.left → F' = F := by
  intro H R K _ _ _ _ _ G G' _ _ G₀ G₀' _ _ φ φ' hG hG' hφ hφ' f hf
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := hG.smooth
  have := hG'.proper
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G _) hφ
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hφ' (isGrpPullback_pullback G' _)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := abelianScheme_hom_extends_dedekind H R K G G' hG hG'
    (a.hom ≫ f ≫ b.hom) inferInstance
  have key : f.left ≫ φ' = φ ≫ F.left := by
    have h₁ := ExtUnique.pullback_map_left_fst (spMap (algebraMap R K)) F
    rw [hF', Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi a.hom.left).1 h₁
  exact ⟨F, hF, key, fun F' h' => ExtUnique.over_hom_ext_of_isPullback (j := spMap (algebraMap R K)) hφ.1 (h'.symm.trans key)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.AHWeil

theorem eq_top_of_add_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (W : Submodule ℂ (Fin g → ℂ)) (h : ∀ z : Fin g → ℂ, ∃ l : Λ, z - (l : Fin g → ℂ) ∈ W) : W = ⊤ := by
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hW : IsClosed (W : Set (Fin g → ℂ)) := W.closed_of_finiteDimensional
  obtain ⟨l, hl⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun l : Λ => (Homeomorph.subRight (l : Fin g → ℂ)) ⁻¹' (W : Set (Fin g → ℂ)))
    (fun l => hW.preimage (Homeomorph.continuous _))
    (Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 (h z))
  rw [← Homeomorph.preimage_interior] at hl
  obtain ⟨z, hz⟩ := hl
  exact W.eq_top_of_nonempty_interior' ⟨_, hz⟩

theorem dim_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g g' : ℕ} (u : HolUnif A L g) (u' : HolUnif A L g')
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z) : g = g' := by
  haveI := u.discrete
  haveI := u'.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := eq_top_of_add_discrete u'.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u'.ex w)
    refine ⟨⟨w - F z, (u'.ker _).1 ?_⟩, z, by simp⟩
    have h := u'.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

theorem tangent_and_weil_of_isAH : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ g = P.g ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
  ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin g → ℂ))) (unitOn c) := by
  intro hT P g u Hm χ hu
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u₀, H₀, χ₀, E₀, hu₀, -, hv, hw, -, -, hE, -, hW⟩ := hT P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  obtain rfl := dim_eq u u₀ F hF
  obtain ⟨⟨Ef, hEf, hB⟩, h1, h2⟩ := unimodular_and_tangent_of_isAH hT P rig hrig u Hm χ hu
  refine ⟨Ef, hEf, hB, rfl, h1, h2, fun k a b c hk hc => ?_⟩
  have ha := (UnifCompare.mem_iff u u₀ F hF a).2 a.2
  have hb := (UnifCompare.mem_iff u u₀ F hF b).2 b.2
  have e : Ef a b = E₀ ⟨F a, ha⟩ ⟨F b, hb⟩ := by
    have h := hE ⟨F a, ha⟩ ⟨F b, hb⟩
    rw [UnifCompare.hermForm_eq P.isLB u u₀ hu hu₀ F hF, ← hEf] at h
    exact_mod_cast h.symm
  have h := hW k ⟨F a, ha⟩ ⟨F b, hb⟩ c hk (e ▸ hc)
  rwa [← map_smul, ← map_smul, hF, hF] at h

end GlobalTheory.AHWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmDatumFormSqrtNegDPurePeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM


open PureTypeVector in
theorem cmDatum_form_sqrtNegD_pure_period {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) {ρ : ℂ}
    (hty : ∀ i, ty i (H.rt : E) = ρ) {x : D.La} (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ((D.EF (H.w0 • x) x : ℤ) : ℝ) = ρ.im * r := by
  obtain ⟨hlin, hinj, -, -, Hm, hH, hpos, hEF⟩ := hP
  have hw0 : Pe (H.w0 • x) = ((1 + ρ) / 2) • Pe x := by
    funext i
    rw [hlin, Pi.smul_apply, smul_eq_mul]
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      simpa [map_ofNat] using this
    have h3 := congrArg (ty i) h2
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hty i] at h3
    rw [← h3]; ring
  set r : ℝ := (hermForm Hm (Pe x) (Pe x)).re with hr
  have hre : hermForm Hm (Pe x) (Pe x) = (r : ℂ) :=
    Complex.ext (by simp [hr]) (by simp [hermForm_self_im hH])
  have hr0 : 0 < r := hpos _ fun h => hx (hinj (by rw [h, map_zero]))
  refine ⟨r / 2, by positivity, ?_⟩
  rw [← hEF, hw0]
  have := hermForm_smul_smul Hm ((1 + ρ) / 2) 1 (Pe x) (Pe x)
  rw [one_smul] at this
  rw [this, hre]
  simp
  ring

theorem definite_datum_form_pos :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ),
      (D.q = 0 ∧ 0 < ((ε : ℤ) : ℝ) * H.rt0.im) ∨ (D.p = 0 ∧ ((ε : ℤ) : ℝ) * H.rt0.im < 0) →
      ∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x := by
  intro E _ _ _ H D ε h x hx
  obtain ⟨g, ty, hty⟩ : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let n : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ, Fin (n τ))).symm
    have key : ∀ τ, Nat.card {i // (e i).1 = τ} = n τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun s => s.1 = τ) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun h => (key τ).trans (if_pos h), fun h => (key τ).trans (if_neg h)⟩⟩
  obtain ⟨Pe, hP⟩ := datum_exists_period E H D g ty hty
  have hcard : ∀ i, Nat.card {j // ty j = ty i} ≠ 0 := fun i =>
    haveI : Nonempty {j // ty j = ty i} := ⟨⟨i, rfl⟩⟩
    Nat.card_pos.ne'
  have key : ∃ ρ : ℂ, (∀ i, ty i (H.rt : E) = ρ) ∧ 0 < ((ε : ℤ) : ℝ) * ρ.im := by
    rcases h with ⟨hq, hε⟩ | ⟨hp, hε⟩
    · refine ⟨H.rt0, fun i => ?_, hε⟩
      by_contra hne
      exact hcard i (((hty (ty i)).2 hne).trans hq)
    · refine ⟨-H.rt0, fun i => ?_, by simpa using hε⟩
      have hne : ty i (H.rt : E) ≠ H.rt0 := fun he => hcard i (((hty (ty i)).1 he).trans hp)
      have h2 : (H.rt : E) ^ 2 = -(H.d : E) := by
        have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
        simpa using this
      have h3 : ty i (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
        rw [← map_pow, h2, H.sqrt_neg_disc_sq]; simp
      exact (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left hne
  obtain ⟨ρ, hρ, hε⟩ := key
  obtain ⟨r, hr, hE⟩ := cmDatum_form_sqrtNegD_pure_period D hP hρ hx
  have : (0 : ℝ) < ((ε : ℤ) : ℝ) * ((D.EF (H.w0 • x) x : ℤ) : ℝ) := by
    rw [hE, ← _root_.mul_assoc]; exact mul_pos hε hr
  exact_mod_cast this

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmGeneratorSqQuadraticEq
section
open NumberField

namespace GlobalTheory.CMGeneratorSquare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cm_generator_sq_quadratic_eq (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.w0 * H.w0 = H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
  have hd : (H.d + 1) = 4 * ((H.d + 1) / 4) := by
    have := H.d_mod; omega
  have h1 : (4 : 𝓞 E) * (H.w0 * H.w0) = 4 * (H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E)) := by
    have h2 := H.two_weight_eq_one_add_root
    have h3 := H.rt_sq
    have h4 : ((H.d + 1 : ℕ) : 𝓞 E) = 4 * (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
      conv_lhs => rw [hd]
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have h5 : (4 : 𝓞 E) * (H.w0 * H.w0) = (2 * H.w0) ^ 2 := by ring
    rw [h5, h2, mul_sub, ← h4]
    push_cast
    linear_combination h3 - 2 * h2
  have h4ne : (4 : 𝓞 E) ≠ 0 := by exact_mod_cast (by norm_num : (4 : ℕ) ≠ 0)
  exact mul_left_cancel₀ h4ne h1

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {a : NumberField.RingOfIntegers E}, a ∈ GlobalTheory.CM.OK H →
    ∃ (u : ℤ) (v : ℤ), a = (↑u : NumberField.RingOfIntegers E) + (↑v : NumberField.RingOfIntegers E) *
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H := by
  intro E _ _ _ H a ha
  set k : ℤ := (((H.d + 1) / 4 : ℕ) : ℤ) with hk
  have hsq : H.w0 * H.w0 = H.w0 - (k : 𝓞 E) := by rw [cm_generator_sq_quadratic_eq H, hk, Int.cast_natCast]
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by rw [hx]; push_cast; ring⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u * u' - v * v' * k, u * v' + v * u' + v * v', ?_⟩
    push_cast
    linear_combination (v * v' : 𝓞 E) * hsq

end GlobalTheory.CMGeneratorSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLieBasisComplex
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.DerivZero

theorem exists_lift_isMonHom {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H]
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hG : IsGrpPullback G' G j φ)
    (hH : IsGrpPullback H' H j ψ) (f : G ⟶ H) [IsMonHom f] :
    ∃ f' : G' ⟶ H', IsMonHom f' ∧ f'.left ≫ ψ = φ ≫ f.left := by
  have w : (φ ≫ f.left) ≫ H.hom = G'.hom ≫ j := by
    rw [Category.assoc, Over.w f]
    exact hG.1.w
  obtain ⟨f', hf'⟩ : ∃ f' : G' ⟶ H', f'.left ≫ ψ = φ ≫ f.left :=
    ⟨Over.homMk (hH.1.lift (φ ≫ f.left) G'.hom w) (hH.1.lift_snd _ _ w), hH.1.lift_fst _ _ w⟩
  have hpt : ∀ {T : Over S'} (x : T ⟶ G'), ∃ x₀ : Over.mk (T.hom ≫ j) ⟶ G, x₀.left = x.left ≫ φ := by
    intro T x
    refine ⟨Over.homMk (x.left ≫ φ) ?_, rfl⟩
    dsimp
    rw [Category.assoc, hG.1.w, ← Category.assoc, Over.w x]
  have hmul : ∀ {T : Over S'} (x y : T ⟶ G'), (x * y) ≫ f' = (x ≫ f') * (y ≫ f') := by
    intro T x y
    obtain ⟨x₀, hx₀⟩ := hpt x
    obtain ⟨y₀, hy₀⟩ := hpt y
    apply Over.OverMorphism.ext
    apply hH.1.hom_ext
    · have e1 := hG.2 T x y x₀ y₀ hx₀ hy₀
      have e2 := hH.2 T (x ≫ f') (y ≫ f') (x₀ ≫ f) (y₀ ≫ f)
        (by simp only [Over.comp_left, hx₀, Category.assoc, hf'])
        (by simp only [Over.comp_left, hy₀, Category.assoc, hf'])
      have e3 : (x₀ * y₀) ≫ f = (x₀ ≫ f) * (y₀ ≫ f) := by
        simp [Hom.mul_def]
      rw [← e2, ← e3]
      simp only [Over.comp_left, Category.assoc, hf', e1]
    · simp only [Over.w]
  refine ⟨f', ⟨?_, ?_⟩, hf'⟩
  · have h1 := hmul (1 : 𝟙_ (Over S') ⟶ G') 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ (Over S') ⟶ G') ≫ f' = 1 := by simpa using h1.symm
    simpa [Hom.one_def] using h2
  · have h3 := hmul (fst G' G') (snd G' G')
    simpa [Hom.mul_def] using h3

end GlobalTheory.DerivZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

namespace TorsionKernelModel

theorem exists_kernel {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] [IsSeparated H.hom] (f : G ⟶ H)
    [IsMonHom f] :
    ∃ (Z : Over S) (_ : GrpObj Z) (i : Z ⟶ G), IsMonHom i ∧ IsClosedImmersion i.left ∧
      IsPullback i (toUnit Z) f η[H] := by
  have hk : IsPullback (pullback.fst f η[H]) (toUnit _) f η[H] := by
    have := IsPullback.of_hasPullback f η[H]
    rwa [toUnit_unique (pullback.snd f η[H]) (toUnit _)] at this
  generalize pullback.fst f η[H] = i at hk
  generalize pullback f η[H] = Z at i hk
  have h₁ : IsClosedImmersion (η[H].left ≫ H.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[H].left := IsClosedImmersion.of_comp _ H.hom
  have h₃ : IsClosedImmersion i.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hk.map (Over.forget S)).flip h₂
  have hm : Mono i := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have hi : i ≫ f = 1 := hk.w
  obtain ⟨_, hG⟩ := exists_grpObj_of_mono i
    (hk.lift η[G] (toUnit _) (by simp))
    (hk.lift ((fst Z Z ≫ i) * (snd Z Z ≫ i)) (toUnit _) (by
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, MonObj.comp_one, MonObj.comp_one, _root_.mul_one,
        Hom.one_def]))
    (hk.lift i⁻¹ (toUnit _) (by rw [GrpObj.inv_comp, hi, inv_one, Hom.one_def]))
    (hk.lift_fst _ _ _) ((hk.lift_fst _ _ _).trans (by rw [Hom.mul_def, lift_fst_comp_snd_comp]))
    ((hk.lift_fst _ _ _).trans (Hom.inv_def _))
  exact ⟨Z, _, i, hG, h₃, hk⟩

theorem isPullback_kernel_baseChange {S S' : Scheme.{0}} (j : S' ⟶ S) {Z G H : Over S} [GrpObj H]
    {i : Z ⟶ G} {f : G ⟶ H} (h : IsPullback i (toUnit Z) f η[H]) :
    IsPullback ((Over.pullback j).map i) (toUnit _) ((Over.pullback j).map f) η[(Over.pullback j).obj H] := by
  refine (h.map (Over.pullback j)).of_iso (Iso.refl _) (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback j)).symm
    (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp) ?_
  simp [Functor.obj.η_def]

theorem isFinite_of_pow_eq_one {S : Scheme.{0}} {Z G : Over S} [GrpObj G] [IsSeparated G.hom] (i : Z ⟶ G)
    [IsClosedImmersion i.left] (n : ℕ) [hn : IsFinite (𝟙 G ^ n).left] (h : i ^ n = 1) : IsFinite Z.hom := by
  have h₁ : IsClosedImmersion (η[G].left ≫ G.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  have e₁ : i ≫ (𝟙 G ^ n) = toUnit Z ≫ η[G] := by
    rw [MonObj.comp_pow, Category.comp_id, h, Hom.one_def]
  have e₂ : i.left ≫ (𝟙 G ^ n).left = Z.hom ≫ η[G].left := by
    rw [← Over.comp_left, e₁]; simp
  let l : Z.left ⟶ pullback (𝟙 G ^ n).left η[G].left := pullback.lift i.left Z.hom e₂
  have h₃ : IsClosedImmersion (l ≫ pullback.fst _ _) := by
    rw [pullback.lift_fst]; infer_instance
  have h₄ : IsClosedImmersion l := IsClosedImmersion.of_comp l (pullback.fst _ _)
  have e₃ : l ≫ pullback.snd _ _ = Z.hom := pullback.lift_snd _ _ _
  rw [← e₃]
  infer_instance

end TorsionKernelModel


open TorsionKernelModel in
theorem exists_abelianScheme_model_of_isogeny_dedekind :
    Out.Laws → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (A₀ B₀ : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] (φ : A₀.left ⟶ P.A.left) (ψ : A₀ ⟶ B₀) (n : ℕ), IsGrpPullback A₀ P.A (spMap (algebraMap R K)) φ → IsAbelianScheme B₀ → IsMonHom ψ → IsFinite ψ.left → Flat ψ.left → Surjective ψ.left → 1 ≤ n → (∀ (T : Over (Sp K)) (x : T ⟶ A₀), x ≫ ψ = 1 → x ^ n = 1) →
  ∃ (B : Over (Sp R)) (_ : GrpObj B) (φB : B₀.left ⟶ B.left) (Ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsGrpPullback B₀ B (spMap (algebraMap R K)) φB ∧ IsMonHom Ψ ∧ IsFinite Ψ.left ∧ Flat Ψ.left ∧ Surjective Ψ.left ∧ ψ.left ≫ φB = φ ≫ Ψ.left := by
  intro hL R K _ _ _ _ _ P A₀ B₀ _ _ φ ψ n hφ hB _ _ _ _ hn hker
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := P.isAb.proper
  have := hB.proper
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback P.A _) hφ
  have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
  obtain ⟨Z, _, i, _, hi, hZ⟩ := exists_kernel (a.hom ≫ ψ)
  obtain ⟨Ga, io, e, _, _, he⟩ := IsogenyModel.exists_flat_closure R K P.A Z i hi
  obtain ⟨_, _, -⟩ := exists_grpObj_of_flat_closed _ P.A Ga io Z i e he
  have hkill : (Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom ≫ ψ = toUnit _ ≫ η[B₀] := by
    rw [← he, Category.assoc, hZ.w, comp_toUnit_assoc]
  have hpow : io ^ n = 1 := by
    apply ExtUnique.pullback_map_injective (spMap (algebraMap R K))
    have h₁ := hker _ ((Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom) (by
      rw [Category.assoc, hkill, Hom.one_def])
    rw [← MonObj.pow_comp, ← MonObj.one_comp a.hom, cancel_mono] at h₁
    exact (map_pow (Over.pullback (spMap (algebraMap R K))).homMonoidHom io n).trans
      (h₁.trans (map_one (Over.pullback (spMap (algebraMap R K))).homMonoidHom).symm)
  have := (hL.mulN _ P n hn).1
  have hfin : IsFinite Ga.hom := isFinite_of_pow_eq_one io n hpow
  have hm : Mono io := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono io.left))
  obtain ⟨B, _, hab, q, _, hq₁, hq₂, hq₃, hq⟩ := hL.quotient R P Ga io ‹_› hm hfin ‹_›
  have hq' := isPullback_kernel_baseChange (spMap (algebraMap R K)) hq
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨β, _, hβ⟩ := flatQuotient_iso_of_same_kernel _ _ _ _ _ _
    ((Over.pullback (spMap (algebraMap R K))).map q) ((Over.pullback (spMap (algebraMap R K))).map io) (a.hom ≫ ψ) i
    inferInstance inferInstance
    (MorphismProperty.overPullbackMap (P := @Flat) _ q hq₂)
    (MorphismProperty.overPullbackMap (P := @Surjective) _ q hq₃)
    (MorphismProperty.overPullbackMap (P := @QuasiCompact) _ q hqc) hq' inferInstance inferInstance
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hZ
    (by rw [← e.inv_hom_id_assoc i, he, Category.assoc, hq'.w, comp_toUnit_assoc]) hkill
  refine ⟨B, _, β.hom.left ≫ pullback.fst B.hom (spMap (algebraMap R K)), q, hab,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback B _)).congr (Category.id_comp _) rfl,
    ‹_›, hq₁, hq₂, hq₃, ?_⟩
  rw [← cancel_epi a.hom.left, ← Category.assoc a.hom.left φ, ha', ← ExtUnique.pullback_map_left_fst, ← hβ]
  simp only [Over.comp_left, Category.assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem PAT.exists_of_sabMap :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S) (t' : SAB H S') (m : SABMap t' T.t f), (∃ T' : PAT H S', T'.t = t' ∧ T'.g = T.g) ∧ LBIso (T.t.PP.L.pull m.φ) t'.PP.L := by
  intro E _ _ _ H S S' f T t' m
  have e : LBIso t'.PP.L (T.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨h₁, h₂, h₃⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S' T.t.G t'.G f m.φ
    T.t.PP.L t'.PP.L T.t.PP.isLB t'.PP.isLB T.ab m.cart e
  have hs : Out.Sym t'.G t'.PP.L := by
    obtain ⟨-, w, hw, -⟩ := t'.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  have hd : SmoothOfRelativeDimension T.g t'.G.hom :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} T.g
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension T.g) m.cart.1 T.dim
  exact ⟨⟨⟨t', h₁, T.g, hd, hs, h₂ T.ample, h₃ T.ktriv⟩, rfl, rfl⟩, LBIso.symm e⟩

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_pat_of_obj :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), ∃ T : PAT H S, T.t = o.t ∧ T.g = Module.finrank ℚ E / 2 * (D.p + D.q) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ o =>
    ⟨⟨o.t, ObjDim.isAbelianScheme o, _, ObjDim.smoothOfRelativeDimension o, ObjDim.sym, o.ample, o.ktriv⟩, rfl, rfl⟩

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfLamEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem kTriv_of_lamEq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L L' : LB A.left), L.IsLB → L'.IsLB → LamEq L' (𝟙 A) (𝟙 A) L (𝟙 A) (𝟙 A) → Out.KTriv A L → Out.KTriv A L' := by
  intro S A _ _ L L' hL hL' h hK R _ t x hx
  have hu : ∃ u : LB.Gen (abelian₂ A (LB.div L L')), u.IsGen := by
    simp only [LamEq, Category.comp_id] at h
    obtain ⟨w, hw⟩ := h
    exact gen_chartPull (GlobalTheory.DescendedPrincipal.chartPullDiv L L' _ _) w hw
  exact hK R t x ((GlobalTheory.UU.KTwist.inK_div_iff (x := x) hL hL' hx).1 (GlobalTheory.UU.KTwist.inK_of_lam (LB.isLB_div hL hL') hu x))

end GlobalTheory.CM
end

