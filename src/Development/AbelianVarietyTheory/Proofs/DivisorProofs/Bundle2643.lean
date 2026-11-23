module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtRationalTorsionUniformisedTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_ext_rational_torsion_uniformised_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → UniTrait D₁.toPre A → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ UniTrait D₂.toPre A₂ ∧ ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, (∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p') ∧ ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.Mum.Enlarge.exists_rational_ext | exact GlobalTheory.Mum.Enlarge.exists_rational_ext | (intros; apply GlobalTheory.Mum.Enlarge.exists_rational_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisationOfTraitUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Ident

theorem finExt_isLocalHom {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    {ρ : R →+* R'} (h : FinExt ρ) : IsLocalHom ρ := by
  letI := ρ.toAlgebra
  have hm : (maximalIdeal R').comap ρ = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (algebraMap _ _) h.2.2.to_isIntegral (maximalIdeal R'))
  exact ((IsLocalRing.local_hom_tfae ρ).out 1 5).2 hm

theorem finExt_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [CommRing R₂]
    [IsDomain R₂] [IsLocalRing R₂] {ρ : R →+* R₁} {ρ' : R₁ →+* R₂} (h : FinExt ρ) (h' : FinExt ρ') :
    FinExt (ρ'.comp ρ) :=
  ⟨h'.1, h'.2.1.comp h.2.1, h'.2.2.comp h.2.2⟩

theorem unif_along_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∀ (D₂ : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U₂ : Unif (maximalIdeal R) D₂ A G) (D₃ : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D₂.toPre D₃.toPre) →
    ∃ (G₃ : Over (Sp R')) (_ : GrpObj G₃) (_ : IsCommMonObj G₃) (β₃ : G₃.left ⟶ G.left) (A₃ : PolAV (Sp (FractionRing R')))
      (U₃ : Unif (maximalIdeal R') D₃ A₃ G₃), IsSemiAbelian G₃ ∧ IsGrpPullback G₃ G (spMap ρ) β₃ ∧
        LBIso U₃.LG.L (U₂.LG.L.pull β₃) := by
  intro R R' _ _ _ _ _ _ ρ hR hf D₂ A G _ _ hG U₂ D₃ h23
  have := hR.2
  haveI := finExt_isLocalHom hf
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D', hD, A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hf.1 ρ hf.2.1 (map_maximalIdeal_le ρ) hG U₂
  have h3' : Nonempty (IsPullDeg (RingHom.id R') D₃.toPre D'.toPre) :=
    GlobalTheory.Mum.isPullDeg_unique_and_comp.1 R R' ρ hf.2.1 D₂.toPre D₃.toPre D'.toPre h23 ⟨hD⟩
  have hG' : IsSemiAbelian ((Over.pullback (specOf ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨U₃, hU₃, -⟩ := (_root_.GlobalTheory.Mum.UnifMove.unif_move R' (maximalIdeal R') hf.1 D₃ D' h3' A' _ hG').1 U'
  have hb : (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ) =
      pullback.fst G.hom (specOf ρ) := Category.id_comp _
  refine ⟨(Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance,
    (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ), A', U₃, hG', ?_, ?_⟩
  · exact (isGrpPullback_pullback G (spMap ρ)).congr rfl hb.symm
  · rw [hU₃]
    exact ⟨hP.lg.choose, hP.lg.choose_spec.1⟩

theorem exists_finExt_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'), IsGrpPullback G' G (spMap φ) β → LBIso U'.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D.toPre D'.toPre) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β₁ : G₁.left ⟶ G.left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β₁ ∧ LBIso U₁.LG.L (P.L.L.pull β₁) := by
  intro R _ _ _ hR D G _ _ P hG W _ _ _ hW φ hφ hloc G' _ _ β D' A' U' hβ hL hD
  have hT : UnifTrait D G P.L.L := ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφ, hloc, hβ, hL, hD⟩
  obtain ⟨R₁, _, _, _, ρ₁, G₁, _, _, β₁, X, _, _, _, hf₁, hβ₁, hQ⟩ := GlobalTheory.Mum.exists_finExt_tq_closedFibre R hR G hG
  haveI hloc₁ : IsLocalHom ρ₁ := finExt_isLocalHom hf₁
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.MumPull.exists_pull R R₁ ρ₁ hf₁.2.1 hloc₁ D
  have hR₁ : Base R₁ := ⟨hf₁.1, by haveI := hR.2; exact charZero_of_injective_ringHom hf₁.2.1⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ₁ (isGrpPullback_pullback G (spMap ρ₁))
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback _ G hG)
  obtain ⟨P₁, w₁, hP₁L, hP₁⟩ := GlobalTheory.UU.exists_cp_pull _ _ (spMap ρ₁) G G₁ β₁ hβ₁.1.w
    (fun T x y => Over.OverMorphism.ext (hβ₁.2 T x y _ _ rfl rfl).symm) P
  have hT₁ : UnifTrait D₁ G₁ P₁.L.L := by
    rw [hP₁L]; exact _root_.GlobalTheory.Mum.TraitExt.unifTrait_pull R R₁ ρ₁ hR hf₁ D D₁ hD₁ G G₁ β₁ hG hβ₁ P.L.L P.L.isLB hT
  have hE : EvenOn P₁ := _root_.GlobalTheory.Mum.evenOn_of_unifTrait R₁ hR₁ D₁ G₁ P₁ hG₁ hT₁ X hQ
  obtain ⟨A, gen, hgen, hA⟩ := _root_.GlobalTheory.Mum.TraitGeneric.exists_polAV_generic R₁ hR₁ D₁ G₁ P₁ hG₁ hT₁
  obtain ⟨D₂, U₂, hU₂, -⟩ := _root_.GlobalTheory.Mum.exists_unif_even R₁ hR₁ G₁ P₁ hG₁ hE A gen hgen hA
  obtain ⟨V, _, _, ψ, D', hψ, h1, h2⟩ := _root_.GlobalTheory.Mum.CommonPull.exists_common_pull R₁ hR₁ D₁ G₁ P₁.L.L P₁.L.isLB hG₁ hT₁ D₂ A U₂ (by rw [hU₂])
  obtain ⟨R', _, _, _, ρ₂, D₃, hf₂, h13, h23⟩ :=
    GlobalTheory.MumRig.exists_common_pull_finite R₁ hR₁ D₁ D₂ V ψ hψ D' h1 h2
  obtain ⟨G₃, _, _, β₃, A₃, U₃, -, hβ₃, hL₃⟩ := unif_along_finExt R₁ R' ρ₂ hR₁ hf₂ D₂ A G₁ hG₁ U₂ D₃ h23
  refine ⟨R', _, _, _, ρ₂.comp ρ₁, D₃, G₃, _, _, β₃ ≫ β₁, A₃, U₃, finExt_comp hf₁ hf₂, ?_, ?_, ?_⟩
  · obtain ⟨a⟩ := hD₁
    obtain ⟨b⟩ := h13
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hf₁.2.1 hf₂.2.1 a b
  · refine (hβ₃.comp hβ₁).congr ?_ rfl
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl
  · rw [hU₂] at hL₃
    have hPP : LBIso P₁.L.L (P.L.L.pull β₁) := ⟨w₁, hP₁.gen⟩
    exact LBIso.trans U₃.LG.isLB (LB.isLB_pull P₁.L.isLB _) (LB.isLB_pull P.L.isLB _) hL₃
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hPP β₃ rfl)

end GlobalTheory.Mum.Ident
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteHomogeneousGeneratorsGradedSubgroup
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmpGen

variable {K : Type} [CommRing K] {D : ℕ}

def twist (x : Fin (D + 1) → K) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial K :=
  MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial K)) (fun l => Polynomial.C (x l) * Polynomial.X)

theorem twist_homog (x : Fin (D + 1) → K) (n : ℕ) (T : MvPolynomial (Fin (D + 1)) ℤ)
    (hT : T.IsHomogeneous n) :
    twist x T = Polynomial.C (aeval x T) * Polynomial.X ^ n := by
  unfold twist
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_eval₂Hom, eval₂_eq', aeval_def, eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have := hT (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul, map_prod, map_pow]
  simp
  ring

def Good (c : ℕ) (A : ℕ → AddSubgroup K) (p : Polynomial K) : Prop :=
  (∀ b < c, p.coeff b = 0) ∧ ∀ q, p.coeff (q + c) ∈ A q

theorem good_zero (c : ℕ) (A : ℕ → AddSubgroup K) : Good c A 0 :=
  ⟨fun _ _ => by simp, fun q => by simpa using (A q).zero_mem⟩

theorem good_add {c : ℕ} {A : ℕ → AddSubgroup K} {p r : Polynomial K} (hp : Good c A p) (hr : Good c A r) :
    Good c A (p + r) :=
  ⟨fun b hb => by simp [hp.1 b hb, hr.1 b hb], fun q => by simpa using (A q).add_mem (hp.2 q) (hr.2 q)⟩

theorem good_int_mul {c : ℕ} {A : ℕ → AddSubgroup K} {p : Polynomial K} (hp : Good c A p) (a : ℤ) :
    Good c A ((a : Polynomial K) * p) := by
  refine ⟨fun b hb => ?_, fun q => ?_⟩
  · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hp.1 b hb, mul_zero]
  · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, ← zsmul_eq_mul]
    exact zsmul_mem (hp.2 q) a

theorem good_mul_X {c : ℕ} {A : ℕ → AddSubgroup K} {p : Polynomial K} (hp : Good c A p) (a : K)
    (hA : ∀ q, ∀ f ∈ A q, a * f ∈ A (q + 1)) :
    Good c A (Polynomial.C a * Polynomial.X * p) := by
  refine ⟨fun b hb => ?_, fun q => ?_⟩
  · rw [mul_assoc, Polynomial.coeff_C_mul]
    rcases b with _ | b
    · simp
    · rw [Polynomial.coeff_X_mul, hp.1 b (by omega), mul_zero]
  · rw [mul_assoc, Polynomial.coeff_C_mul]
    rcases q with _ | q
    · rcases c with _ | c
      · simp
      · rw [zero_add, Polynomial.coeff_X_mul, hp.1 c (by omega), mul_zero]; exact (A 0).zero_mem
    · rw [show q + 1 + c = (q + c) + 1 by omega, Polynomial.coeff_X_mul]
      exact hA q _ (hp.2 q)

theorem good_twist_mul (x : Fin (D + 1) → K) {c : ℕ} {A : ℕ → AddSubgroup K}
    (hA : ∀ q l, ∀ f ∈ A q, x l * f ∈ A (q + 1)) (r : MvPolynomial (Fin (D + 1)) ℤ) :
    ∀ p : Polynomial K, Good c A p → Good c A (twist x r * p) := by
  induction r using MvPolynomial.induction_on with
  | C a => intro p hp; simpa [twist] using good_int_mul hp a
  | add r s hr hs => intro p hp; rw [map_add (f := _), add_mul]; exact good_add (hr p hp) (hs p hp)
  | mul_X r l hr =>
    intro p hp
    have h1 : twist x (r * X l) * p = twist x r * (Polynomial.C (x l) * Polynomial.X * p) := by
      simp [twist]; ring
    rw [h1]
    exact hr _ (good_mul_X hp (x l) (hA · l))

theorem exists_finite_homogeneous_generators : ∀ (K : Type) [CommRing K] (D c : ℕ) (x : Fin (D + 1) → K) (ι : Type) [Fintype ι] (w : ι → K) (Λ : ℕ → AddSubgroup K), (∀ q l, ∀ f ∈ Λ q, x l * f ∈ Λ (q + 1)) → (∀ q, ∀ f ∈ Λ q, ∃ T : ι → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, aeval x (T i) * w i) → ∃ G : Finset (ℕ × K), (∀ g ∈ G, g.2 ∈ Λ g.1) ∧ ∀ q, Λ q ≤ AddSubgroup.closure {f | ∃ g ∈ G, ∃ α : Fin (D + 1) → ℕ, ∑ l, α l + g.1 = q ∧ f = (∏ l, x l ^ α l) * g.2} := by
  intro K _ D c x ι _ w Λ hx hw
  classical
  letI : Module (MvPolynomial (Fin (D + 1)) ℤ) (Polynomial K) := (twist x).toModule
  have hsmul : ∀ (r : MvPolynomial (Fin (D + 1)) ℤ) (p : Polynomial K), r • p = twist x r * p := fun _ _ => rfl
  let S : Set (ℕ × K) := {g | g.2 ∈ Λ g.1}
  let v : ℕ × K → Polynomial K := fun g => Polynomial.C g.2 * Polynomial.X ^ (g.1 + c)
  let M : Submodule (MvPolynomial (Fin (D + 1)) ℤ) (Polynomial K) :=
    Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (v '' S)
  let ψ : (ι → MvPolynomial (Fin (D + 1)) ℤ) →ₗ[MvPolynomial (Fin (D + 1)) ℤ] Polynomial K :=
    Fintype.linearCombination (MvPolynomial (Fin (D + 1)) ℤ) (fun i => Polynomial.C (w i))
  have hle : M ≤ LinearMap.range ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨q, f⟩, hf, rfl⟩
    obtain ⟨T, hT, rfl⟩ := hw q f hf
    refine ⟨T, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ψ, v, Fintype.linearCombination_apply, hsmul, twist_homog x _ _ (hT _), map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul]; ring
  have hfg : M.FG := by
    have h1 : (M.comap ψ).FG := IsNoetherian.noetherian _
    have h2 := h1.map ψ
    rwa [Submodule.map_comap_eq_of_le hle] at h2
  obtain ⟨S0, hS0⟩ := hfg
  have hT : ∀ s ∈ S0, ∃ T : Finset (Polynomial K), ↑T ⊆ v '' S ∧
      s ∈ Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (T : Set (Polynomial K)) := fun s hs =>
    Submodule.mem_span_finite_of_mem_span (by
      have h := Submodule.subset_span (R := MvPolynomial (Fin (D + 1)) ℤ) (s := (S0 : Set (Polynomial K))) hs
      rw [hS0] at h; exact h)
  choose! Tf hTf hsT using hT
  obtain ⟨G, hGS, hGT⟩ := (Finset.subset_set_image_iff (s := S) (t := S0.biUnion Tf) (f := v)).mp (by
    intro p hp
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hp
    obtain ⟨s, hs, hp⟩ := hp
    exact hTf s hs hp)
  refine ⟨G, fun g hg => hGS hg, ?_⟩
  set A : ℕ → AddSubgroup K := fun q => AddSubgroup.closure
    {f | ∃ g ∈ G, ∃ α : Fin (D + 1) → ℕ, ∑ l, α l + g.1 = q ∧ f = (∏ l, x l ^ α l) * g.2} with hAdef
  have hA : ∀ q l, ∀ f ∈ A q, x l * f ∈ A (q + 1) := by
    intro q l f hf
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
      obtain ⟨g, hg, α, hα, rfl⟩ := hf
      refine AddSubgroup.subset_closure ⟨g, hg, α + Pi.single l 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
        simp; omega
      · have : ∏ i, x i ^ (Pi.single l 1 : Fin (D + 1) → ℕ) i = x l := by
          rw [Finset.prod_eq_single l (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
          simp
        simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, this]; ring
    | zero => simpa using (A (q + 1)).zero_mem
    | add a b _ _ ha hb => rw [mul_add]; exact (A (q + 1)).add_mem ha hb
    | neg a _ ha => rw [mul_neg]; exact (A (q + 1)).neg_mem ha
  have hgood : ∀ p ∈ Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (v '' (G : Set (ℕ × K))), Good c A p := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨g, hg, rfl⟩ := hp
      refine ⟨fun b hb => ?_, fun q => ?_⟩
      · simp only [v, Polynomial.coeff_C_mul_X_pow]; rw [if_neg (by omega)]
      · simp only [v, Polynomial.coeff_C_mul_X_pow]
        by_cases hq : q = g.1
        · subst hq; rw [if_pos rfl]
          exact AddSubgroup.subset_closure ⟨g, hg, 0, by simp, by simp⟩
        · rw [if_neg (by omega)]; exact (A q).zero_mem
    | zero => exact good_zero c A
    | add a b _ _ ha hb => exact good_add ha hb
    | smul r a _ ha => rw [hsmul]; exact good_twist_mul x hA r a ha
  intro q f hf
  have hmem : v (q, f) ∈ Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (v '' (G : Set (ℕ × K))) := by
    rw [← Finset.coe_image, hGT]
    have : v (q, f) ∈ M := Submodule.subset_span ⟨(q, f), hf, rfl⟩
    rw [← hS0] at this
    refine Submodule.span_le.mpr ?_ this
    intro s hs
    exact Submodule.span_mono (by
      intro p hp; simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]; exact ⟨s, hs, hp⟩) (hsT s hs)
  have h := (hgood _ hmem).2 q
  simp only [v, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at h
  exact h

end GlobalTheory.HSAmpGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePow
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.ChartRed

def twoRing {R R' A A' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} [CommRing A]
    [Bialgebra R A] [CommRing A'] [Bialgebra R' A'] (f : SemiBialgHom σ A A') :
    A ⊗[R] A →+* A' ⊗[R'] A' where
  toFun := f.two
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    simp only [Algebra.TensorProduct.one_def, TensorProduct.map_tmul, SemiBialgHom.lin_apply,
      map_one f.toRingHom]
  map_mul' x y := by
    induction x with
    | add a b ha hb => simp only [add_mul, map_add (f := _), ha, hb]
    | tmul a b =>
      induction y with
      | add u v hu hv => simp only [mul_add, map_add (f := _), hu, hv]
      | tmul u v => simp [SemiBialgHom.lin_apply, map_mul f.toRingHom]

theorem ev₂_map {p m d : ℕ} {O k : Type} [CommRing O] [CommRing k] {r : O →+* k}
    {G : PDivGroup p O} {G' : PDivGroup p k} (s : SemiHom r G' G) (c : QLog.Chart G d)
    (c' : Katz.Chart G' d) (hc : ∀ n i, c'.x n i = s.app n (c.x n i)) (hp : (p : k) ^ m = 0)
    (n : ℕ) (f : MvPowerSeries (Fin d ⊕ Fin d) O) :
    c'.ev₂ n (map r f) = (s.app n).two (c.ev₂ n f) := by
  have e : (fun i => twoRing (s.app n)
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] 1) (fun i => 1 ⊗ₜ[O] c.x n i) i)) = c'.x₂ n := by
    funext i
    cases i with
    | inl i =>
      change (s.app n) (c.x n i) ⊗ₜ[k] (s.app n) 1 = c'.x n i ⊗ₜ[k] 1
      rw [map_one, hc]
    | inr i =>
      change (s.app n) 1 ⊗ₜ[k] (s.app n) (c.x n i) = 1 ⊗ₜ[k] c'.x n i
      rw [map_one, hc]
  have h := _root_.GlobalTheory.algHom_eval_comp_eq_evA_map p m O _ k (G'.A n ⊗[k] G'.A n) _ _ _ (c.isEval₂ n) r (twoRing (s.app n))
    (fun a => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        ← map_one (twoRing (s.app n))]
      exact map_smulₛₗ (s.app n).two a 1)
    (by rw [← map_natCast (algebraMap k _), ← map_pow, hp, map_zero])
    (fun i => (congrFun e i).symm ▸ c'.nil₂ n i) f
  refine Eq.trans ?_ h.symm
  unfold Katz.Chart.ev₂
  congr 2
  exact e.symm

theorem exists_chart : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I → ∃ c' : Katz.Chart (G.baseChange (O ⧸ I)) d, c'.IsLawOf (fun i => map (Ideal.Quotient.mk I) (c.μ i)) ∧ (∀ n f, c'.ev n (map (Ideal.Quotient.mk I) f) = (G.toBase (O ⧸ I)).app n (c.ev n f)) ∧ ∀ n s, c'.ev₂ n (map (Ideal.Quotient.mk I) s) = ((G.toBase (O ⧸ I)).app n).two (c.ev₂ n s) := by
  intro p _ O _ G d c I m hm
  obtain ⟨hx, h1, h2⟩ := T.formalChart_presents_levels_mod_ideal p O G d c I m hm
  have hp : (p : O ⧸ I) ^ m = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hm
  let c' : Katz.Chart (G.baseChange (O ⧸ I)) d :=
    { x := fun n i => (G.toBase (O ⧸ I)).app n (c.x n i)
      nil := hx
      res := fun n i => ((G.toBase (O ⧸ I)).res_app n _).trans (congrArg _ (c.res n i))
      aug := fun n i => by rw [((G.toBase (O ⧸ I)).app n).counit_map, c.aug, map_zero]
      presents := h2 }
  have h3 := ev₂_map (G.toBase (O ⧸ I)) c c' (fun _ _ => rfl) hp
  refine ⟨c', fun n i => ?_, h1, h3⟩
  exact (h3 n (c.μ i)).trans ((congrArg _ (c.comul n i)).trans
    (((G.toBase (O ⧸ I)).app n).two_comul _))

end GlobalTheory.QLog.ChartRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisActionOnUniformisedGroupPulledData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem galAct_exists : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  intro R R' _ _ _ _ _ _ ρ hB hF hG D D' hD A' G' _ _ hS U'
  exact _root_.GlobalTheory.Mum.galAct_nonempty R hB R' ρ hF hG D D' hD A' G' hS U'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreProductSumPolarisedAbelianVari
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdGen

theorem isMonHom_of_lift {S : Scheme.{0}} {H A A₁ A₂ : Over S} [GrpObj H] [GrpObj A] [GrpObj A₁] [GrpObj A₂]
    (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsMonHom a₁] [IsMonHom a₂] [IsIso (lift a₁ a₂)] (f : H ⟶ A)
    [IsMonHom (f ≫ a₁)] [IsMonHom (f ≫ a₂)] : IsMonHom f := by
  have ext : ∀ {T : Over S} (a b : T ⟶ A), a ≫ a₁ = b ≫ a₁ → a ≫ a₂ = b ≫ a₂ → a = b :=
    fun a b h₁ h₂ => (cancel_mono (lift a₁ a₂)).1 (by rw [comp_lift, comp_lift, h₁, h₂])
  constructor
  · refine ext _ _ ?_ ?_ <;> rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine ext _ _ ?_ ?_ <;>
      rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        tensorHom_comp_tensorHom]

theorem exists_iso_prod {S S' : Scheme.{0}} (j : S' ⟶ S) (G₁ G₂ : Over S) {A A₁ A₂ : Over S'}
    (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsIso (lift a₁ a₂)] (e₁ : (Over.pullback j).obj G₁ ≅ A₁)
    (e₂ : (Over.pullback j).obj G₂ ≅ A₂) :
    ∃ e : (Over.pullback j).obj (G₁ ⊗ G₂) ≅ A,
      e.hom ≫ a₁ = (Over.pullback j).map (fst G₁ G₂) ≫ e₁.hom ∧
      e.hom ≫ a₂ = (Over.pullback j).map (snd G₁ G₂) ≫ e₂.hom := by
  have h₁ : inv (lift a₁ a₂) ≫ a₁ = fst A₁ A₂ := by rw [IsIso.inv_comp_eq, lift_fst]
  have h₂ : inv (lift a₁ a₂) ≫ a₂ = snd A₁ A₂ := by rw [IsIso.inv_comp_eq, lift_snd]
  refine ⟨prodComparisonIso (Over.pullback j) G₁ G₂ ≪≫ (e₁ ⊗ᵢ e₂) ≪≫ (asIso (lift a₁ a₂)).symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, h₁, tensorIso_hom, tensorHom_fst,
      prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_fst_assoc]
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, h₂, tensorIso_hom, tensorHom_snd,
      prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd_assoc]


open GlobalTheory.CechPic in
theorem cls_extLB {X X₁ X₂ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (hL : L.IsLB) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (hw : w.IsGen) :
    cls L hL = pull f₁ (cls L₁ h₁) + pull f₂ (cls L₂ h₂) :=
  (cls_eq_iff hL (isLB_extLB h₁ h₂ f₁ f₂)).2 ⟨w, hw⟩


open GlobalTheory.CechPic in
theorem exists_gen_prod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (A : PolAV (Sp (FractionRing R))) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ gen : (Over.pullback (jK R)).obj (G₁ ⊗ G₂) ≅ A.A, IsMonHom gen.hom ∧ gen.hom ≫ a₁ = (Over.pullback (jK R)).map (fst G₁ G₂) ≫ U₁.gen.hom ∧ gen.hom ≫ a₂ = (Over.pullback (jK R)).map (snd G₁ G₂) ≫ U₂.gen.hom ∧ ∀ (L : LB (G₁ ⊗ G₂).left) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → wL.IsGen → ∃ w : LB.Iso (A.L.pull gen.hom.left) (L.pull (pullback.fst (G₁ ⊗ G₂).hom (jK R))), w.IsGen := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ A a₁ a₂ hA
  haveI := hA.hom₁
  haveI := hA.hom₂
  haveI := hA.lim
  haveI := U₁.gen_hom
  haveI := U₂.gen_hom
  obtain ⟨e, e₁, e₂⟩ := exists_iso_prod (jK R) G₁ G₂ a₁ a₂ U₁.gen U₂.gen
  haveI : IsMonHom (e.hom ≫ a₁) := by rw [e₁]; infer_instance
  haveI : IsMonHom (e.hom ≫ a₂) := by rw [e₂]; infer_instance
  refine ⟨e, isMonHom_of_lift a₁ a₂ e.hom, e₁, e₂, fun L wL hL hwL => ?_⟩
  obtain ⟨wA, hwA⟩ := hA.w
  have cA := cls_extLB A.isLB A₁.isLB A₂.isLB wA hwA
  have cL := cls_extLB hL U₁.LG.isLB U₂.LG.isLB wL hwL
  have c₁ : pull U₁.gen.hom.left (cls _ A₁.isLB) = pull (pullback.fst G₁.hom (jK R)) (cls _ U₁.LG.isLB) :=
    (cls_eq_iff (pull_isLB A₁.isLB _) (pull_isLB U₁.LG.isLB _)).2 U₁.ext
  have c₂ : pull U₂.gen.hom.left (cls _ A₂.isLB) = pull (pullback.fst G₂.hom (jK R)) (cls _ U₂.LG.isLB) :=
    (cls_eq_iff (pull_isLB A₂.isLB _) (pull_isLB U₂.LG.isLB _)).2 U₂.ext
  have l₁ : e.hom.left ≫ a₁.left = ((Over.pullback (jK R)).map (fst G₁ G₂)).left ≫ U₁.gen.hom.left :=
    congrArg (fun z => z.left) e₁
  have l₂ : e.hom.left ≫ a₂.left = ((Over.pullback (jK R)).map (snd G₁ G₂)).left ≫ U₂.gen.hom.left :=
    congrArg (fun z => z.left) e₂
  have m₁ : ((Over.pullback (jK R)).map (fst G₁ G₂)).left ≫ pullback.fst G₁.hom (jK R) =
      pullback.fst (G₁ ⊗ G₂).hom (jK R) ≫ (fst G₁ G₂).left := pullback.lift_fst _ _ _
  have m₂ : ((Over.pullback (jK R)).map (snd G₁ G₂)).left ≫ pullback.fst G₂.hom (jK R) =
      pullback.fst (G₁ ⊗ G₂).hom (jK R) ≫ (snd G₁ G₂).left := pullback.lift_fst _ _ _
  have d₁ : pull e.hom.left (pull a₁.left (cls _ A₁.isLB)) =
      pull (pullback.fst (G₁ ⊗ G₂).hom (jK R)) (pull (fst G₁ G₂).left (cls _ U₁.LG.isLB)) :=
    (pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) l₁).trans ((pull_comp _ _ _).trans
      ((congrArg _ c₁).trans ((pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) m₁).trans
        (pull_comp _ _ _))))))
  have d₂ : pull e.hom.left (pull a₂.left (cls _ A₂.isLB)) =
      pull (pullback.fst (G₁ ⊗ G₂).hom (jK R)) (pull (snd G₁ G₂).left (cls _ U₂.LG.isLB)) :=
    (pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) l₂).trans ((pull_comp _ _ _).trans
      ((congrArg _ c₂).trans ((pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) m₂).trans
        (pull_comp _ _ _))))))
  exact (cls_eq_iff (pull_isLB A.isLB _) (pull_isLB hL _)).1
    ((congrArg (pull e.hom.left) cA).trans ((map_add _ _ _).trans ((congrArg₂ (· + ·) d₁ d₂).trans
      ((map_add _ _ _).symm.trans (congrArg (pull (pullback.fst (G₁ ⊗ G₂).hom (jK R))) cL).symm))))

end GlobalTheory.ProdGen
end

