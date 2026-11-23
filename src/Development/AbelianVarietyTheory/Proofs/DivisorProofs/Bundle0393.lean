module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveEventuallyFilteredColimitAlgebraStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_eventually_filteredColimit_algebra : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧ Module.Projective c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Projective (F.obj k) (F.obj k ⊗[F.obj j] A) := by
  first | (exact @GlobalTheory.ProjColim.projective_eventually) | (exact GlobalTheory.ProjColim.projective_eventually) | (intros; apply GlobalTheory.ProjColim.projective_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropFTopHolds
section
open GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem laurentPi_bijective : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)], Function.Bijective (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) := by
  intro n B _
  have hap : ∀ (x : LaurentPolynomial (∀ j, B j)) k, (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) x k = laurentMap (Pi.evalRingHom B k) x := fun _ _ => rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro p hp
    have hc : p.coeff = 0 := by
      ext m j
      have h1 := congrArg (fun r : ∀ j, LaurentPolynomial (B j) => (r j).coeff m) hp
      simp only [hap, Pi.zero_apply, laurentMap_coeff, Finsupp.mapRange_apply] at h1
      simpa using h1
    exact AddMonoidAlgebra.ext hc
  · intro F
    have hsub : ∀ j (q : LaurentPolynomial (B j)), Pi.single j q ∈ (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)).range := by
      intro j q
      induction q using LaurentPolynomial.induction_on' with
      | add p r hp hr =>
        rw [Pi.single_add]; exact Subring.add_mem _ hp hr
      | C_mul_T m a =>
        refine ⟨LaurentPolynomial.C (Pi.single j a) * LaurentPolynomial.T m, ?_⟩
        funext k
        simp only [hap, map_mul, laurentMap_C, laurentMap_T, Pi.evalRingHom_apply]
        by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_eq_of_ne hk]
    rw [← Finset.univ_sum_single F]
    obtain ⟨p, hp⟩ := Subring.sum_mem _ (fun j (_ : j ∈ Finset.univ) => hsub j (F j))
    exact ⟨p, hp⟩

end GlobalTheory.EtC.GmStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiGPairingEqChGPairing
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem psiG_pairing_eq_chG_pairing : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ)
    (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y →
    ∑ᶠ x, psiG S n x * star (Y x) = ∑ᶠ x, chG S n x * star (Y x) := by
  intro F _ _ S n Y hY hF
  have hfin : Finite (GL (Fin n) F) := inferInstance
  have hfs : ∀ f : GL (Fin n) F → ℂ, (Function.support f).Finite := fun f => Set.toFinite _
  have hz : ∀ a ∈ Finset.range n,
      ∑ᶠ x, hc a (n - a) (psiG S a) (fun _ => 1) n x * star (Y x) = 0 := by
    intro a ha
    have ha' : a < n := Finset.mem_range.mp ha
    exact GlobalTheory.T.harishChandraInductionGL_trivial_orthogonal_hyperplaneFixer F a (n - a) n (by omega) (by omega) (psiG S a) Y hY hF
  have hrec : ∀ x, psiG S n x * star (Y x) = chG S n x * star (Y x)
      - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x * star (Y x) := by
    intro x
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F S n x, sub_mul, Finset.sum_mul]
  simp_rw [hrec]
  rw [finsum_sub_distrib (hfs _) (hfs _), finsum_sum_comm (Finset.range n) _ (fun a _ => hfs _),
    Finset.sum_eq_zero hz, sub_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RebasedTypicalCurvesIsBasis
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory.DepthStages.RebaseBasis

theorem rebase_isBasis : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (X : Matrix (Fin d) (Fin d) C),
      IsBasis G p ty γ → (∀ a b, IsIntV v (X a b)) → v X.det = 0 →
      (∀ a b, X a b ≠ 0 → ty b = ty a) →
      IsBasis G p ty (rebase G X γ) ∧
        (∀ a, tangent (rebase G X γ a) = ∑ b, X a b • tangent (γ b)) ∧
        ∀ a n, G.lc p (rebase G X γ a) n = ∑ b, X a b ^ (p ^ n) • G.lc p (γ b) n := by
  intro C _ _ _ v p hp hv d h ty G γ X hB hX hdet hty
  obtain ⟨hγc, hγty, hγdet⟩ := hB
  have key : ∀ a, _ := fun a => pt6' C v p hp hv d d G γ (X a) hγc (hX a)
  have hlc : ∀ a n, G.lc p (rebase G X γ a) n = ∑ b, X a b ^ (p ^ n) • G.lc p (γ b) n :=
    fun a n => (key a).2.2.1 n
  have htan : ∀ a, tangent (rebase G X γ a) = ∑ b, X a b • tangent (γ b) := fun a => (key a).2.1
  refine ⟨⟨fun a => (key a).1, fun a => ⟨(key a).2.2.2 fun b => (hγty b).1, ?_⟩, ?_⟩, htan, hlc⟩
  · intro n c hc
    rw [hlc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hXab : X a b = 0
    · rw [hXab, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul]
    · have hb := hty a b hXab
      rw [(hγty b).2 n c (by rw [hb]; exact hc), mul_zero]
  · have hM : (Matrix.of fun a b => tangent (rebase G X γ a) b) =
        X * Matrix.of fun a b => tangent (γ a) b := by
      ext a b
      rw [Matrix.of_apply, htan, Matrix.mul_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hM, Matrix.det_mul, v.map_mul, hdet, hγdet, add_zero]

end GlobalTheory.DepthStages.RebaseBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFunctionalVanishesOnOmegaFormsStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_functional_vanishes_on_omega_forms : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∀ (i : Fin (d + 1)) (I : Finset (Fin (d + 1))), I.Nonempty → i ∉ I → ∀ y ∈ omA k x I, ρ y = 0 := by
  first | (exact @GlobalTheory.PD.ResVan.resvan) | (exact GlobalTheory.PD.ResVan.resvan) | (intros; apply GlobalTheory.PD.ResVan.resvan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivWordExpCoordsDifferentialOperator
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.WordExp

theorem isSmoothFun_foldr {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    {f : G → ℂ} (hf : h.IsSmoothFun f) : ∀ l : List 𝔤, h.IsSmoothFun (l.foldr h.rightDeriv f)
  | [] => hf
  | X :: l => h.isSmoothFun_rightDeriv (isSmoothFun_foldr h hf l) X

end GlobalTheory.WordExp

theorem GlobalTheory.WordExp.word_apOp : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ l : List 𝔤, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ x ∈ Metric.ball (0 : E d) r, l.foldr h.rightDeriv f (h.expG (coordEquiv b (x))) = apOp l.length a (fun y => f (h.expG (coordEquiv b (y)))) x := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b r c hyp l
  obtain ⟨hc, -, hX⟩ := hyp
  induction l with
  | nil =>
    refine ⟨fun _ _ _ => 1, fun _ _ => contDiffOn_const, fun f _ x _ => ?_⟩
    simp only [List.foldr_nil, List.length_nil]
    rw [apOp_zero_one]
  | cons X l ih =>
    obtain ⟨a, ha, hl⟩ := ih
    have hcX : ∀ j, ContDiffOn ℝ ∞ (fun x : E d => ((c X j x : ℝ) : ℂ)) (Metric.ball 0 r) := fun j =>
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hc X j)
    obtain ⟨a', ha', -, hcomp⟩ := GlobalTheory.VFComp.vectorField_comp d l.length (Metric.ball 0 r)
      Metric.isOpen_ball a (fun j x => ((c X j x : ℝ) : ℂ)) ha hcX
    refine ⟨a', ha', fun f hf x hx => ?_⟩
    simp only [List.foldr_cons, List.length_cons]
    have hF := GlobalTheory.WordExp.isSmoothFun_foldr h hf l
    rw [hX _ hF X x hx]
    have heq : (fun y : E d => l.foldr h.rightDeriv f (h.expG (coordEquiv b y))) =ᶠ[nhds x]
        apOp l.length a (fun y => f (h.expG (coordEquiv b y))) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy using hl f hf y hy
    have hu : ContDiffOn ℝ ∞ (fun y : E d => f (h.expG (coordEquiv b y))) (Metric.ball 0 r) := by
      have := h.contDiff_comp_coordEquiv hf 1 b
      simp only [one_mul] at this
      exact this.contDiffOn
    rw [heq.fderiv_eq]
    exact hcomp _ hu x hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootExtractionLemmaSheaf
section
namespace GlobalTheory.RootTrick

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem root_statement : RootStatement := by
  intro C _ _ _ v p hp hv d h m ty i G γ hγ hty n j _hn V _ _ La hdim
  obtain ⟨x, hxi, hxd, hxk⟩ := _root_.GlobalTheory.powRow_matrix C v V (p ^ n) (pow_pos hp.pos n) j m
    (fun u => La (G.lc p (γ u) n)) hdim
  refine ⟨x, hxi, hxd, ?_⟩
  have h6 := fun w => pt6' C v p hp hv d m G γ (x w) hγ (hxi w)
  dsimp only at h6 ⊢
  refine ⟨fun w => (h6 w).2.1, fun w => ⟨(h6 w).2.2.2 (fun u => (hty u).1), fun k a hk => ?_⟩,
    fun w hw => ?_⟩
  · rw [(h6 w).2.2.1 k]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, (hty _).2 k a hk, mul_zero,
      Finset.sum_const_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [(h6 w).2.2.1 n, map_sum]
      simp only [map_smul]
      exact hxk w hw

end GlobalTheory.RootTrick
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityEtaleLocallyPowPrimitiveRoot
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.RootLoc

theorem root_loc_pow_prim : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ ω : (Γ(U, ⊤))ˣ, ω ^ q = 1 →
    Loc U fun V g => ∃ (ζ : Prim q Γ(V, ⊤)) (a : ℕ), (Units.map g.appTop.hom.toMonoidHom ω : Γ(V, ⊤)) = ζ.1 ^ a := by
  intro q _ U hq ω hω
  apply GlobalTheory.EtC.loc_trans
  refine GlobalTheory.EtC.loc_mono _ _ _ ((PrimLoc.prim_loc q U).1 hq) ?_
  rintro V g ⟨ζ⟩
  have hx : (g.appTop.hom (ω : Γ(U, ⊤))) ^ q = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hω, Units.val_one, map_one]
  refine GlobalTheory.EtC.loc_mono _ _ _ ((PrimLoc.prim_loc q V).2.2.1 ζ _ hx) ?_
  rintro W k ⟨a, ha⟩
  refine ⟨ζ.map k.appTop.hom, a, ?_⟩
  rw [Units.coe_map]
  exact (PrimLoc.appTop_comp g k _).trans ha

end GlobalTheory.EtC.RootLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootTrickFinsetCurvesBlockInverse
section
namespace GlobalTheory.RootFin

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

open MvPowerSeries in
private lemma sum_dite_mem_eq_sum_equivFin {d : ℕ} (S : Finset (Fin d)) {M : Type*} [AddCommMonoid M] (F : S → M) :
    ∑ b, (if hb : b ∈ S then F ⟨b, hb⟩ else 0) = ∑ w : Fin S.card, F (S.equivFin.symm w) := by
  rw [Equiv.sum_comp S.equivFin.symm F,
    ← Finset.sum_subset (Finset.subset_univ S) (fun b _ hb => by simp [hb]), ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl (fun b _ => by simp [b.2])

open MvPowerSeries in
private lemma lc_sumF_eq_sum {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d m : ℕ} (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (p : ℕ)
    (g : Fin m → Fin d → PowerSeries C) (hg : ∀ u, _root_.ReciprocityTheory.PGsh.IsCurve v (g u)) (n : ℕ) :
    G.lc p (G.sumF g) n = ∑ u, G.lc p (g u) n := by
  funext c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.ReciprocityTheory.PGsh.LogFGL.lc, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_sumF G g hg c, map_sum, Finset.sum_apply]

open MvPowerSeries in
private lemma lc_rescaleCurve_eq_pow_smul {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (p : ℕ)
    (x : C) {ga : Fin d → PowerSeries C} (hga : _root_.ReciprocityTheory.PGsh.IsCurve v ga) (n : ℕ) :
    G.lc p (_root_.ReciprocityTheory.PGsh.rescaleCurve x ga) n = x ^ (p ^ n) • G.lc p ga n := by
  funext c
  simp only [_root_.ReciprocityTheory.PGsh.LogFGL.lc, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_rescale G x (fun b => (hga b).1) c, PowerSeries.coeff_rescale, Pi.smul_apply, smul_eq_mul]


open MvPowerSeries in
theorem _root_.GlobalTheory.RootFin.root_fin : _root_.ReciprocityTheory.ChartRestriction.G.Sh.RootStatement → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (i : ZMod h) (G : _root_.ReciprocityTheory.PGsh.LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (S : Finset (Fin d)),
      (∀ a ∈ S, _root_.ReciprocityTheory.PGsh.IsCurve v (γ a)) → (∀ a ∈ S, G.IsOfType p ty i (γ a)) → ∀ (n j : ℕ), 1 ≤ n →
      ∀ (V : Type) [AddCommGroup V] [Module C V] (La : (Fin d → C) →ₗ[C] V),
        Module.finrank C (Submodule.span C
          ((fun a => La (G.lc p (γ a) n)) '' (S : Set (Fin d)))) ≤ j →
        ∃ (x y : Matrix (Fin d) (Fin d) C) (D : Finset (Fin d)), D ⊆ S ∧ D.card ≤ j ∧
          (∀ a b, _root_.ReciprocityTheory.PGsh.IsIntV v (x a b)) ∧ (∀ a b, _root_.ReciprocityTheory.PGsh.IsIntV v (y a b)) ∧
          (∀ a b, x a b ≠ 0 → a ∈ S ∧ b ∈ S) ∧ (∀ a b, y a b ≠ 0 → a ∈ S ∧ b ∈ S) ∧
          (∀ a c, a ∈ S → c ∈ S → ∑ b, x a b * y b c = if a = c then 1 else 0) ∧
          ∀ a ∈ S, a ∉ D → La (∑ b, x a b ^ (p ^ n) • G.lc p (γ b) n) = 0 := by
  intro hroot C _ _ _ v p hp hv d h ty i G γ S hcurve htype n j hn V _ _ La hrank
  set e : Fin S.card ≃ S := S.equivFin.symm with he
  set γS : Fin S.card → Fin d → PowerSeries C := fun u => γ (e u) with hγS
  have hcS : ∀ u, _root_.ReciprocityTheory.PGsh.IsCurve v (γS u) := fun u => hcurve _ (e u).2
  have htS : ∀ u, G.IsOfType p ty i (γS u) := fun u => htype _ (e u).2
  have hrange : Set.range (fun u => La (G.lc p (γS u) n)) = (fun a => La (G.lc p (γ a) n)) '' (S : Set (Fin d)) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨e u, (e u).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨e.symm ⟨a, ha⟩, by simp [γS]⟩
  obtain ⟨T, hTint, hTdet, hrest⟩ := hroot C v p hp hv d h S.card ty i G γS hcS htS n j hn V La (hrange ▸ hrank)
  obtain ⟨-, -, hTzero⟩ := hrest
  have hTinv := _root_.ReciprocityTheory.ChartRestriction.G.Sh.pt_inv_int (fun a b => (_root_.ReciprocityTheory.ChartRestriction.G.Sh.ptIsIntV_iff _).mp (hTint a b)) hTdet
  have hzero : _root_.ReciprocityTheory.PGsh.IsIntV v (0 : C) := (_root_.ReciprocityTheory.ChartRestriction.G.Sh.ptIsIntV_iff _).mpr (Subring.zero_mem _)
  set x : Matrix (Fin d) (Fin d) C := fun a b =>
    if ha : a ∈ S then if hb : b ∈ S then T (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) else 0 else 0 with hx
  set y : Matrix (Fin d) (Fin d) C := fun a b =>
    if ha : a ∈ S then if hb : b ∈ S then T⁻¹ (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) else 0 else 0 with hy
  set D : Finset (Fin d) := (Finset.univ.filter (fun w : Fin S.card => (w : ℕ) < j)).image (fun w => (e w : Fin d)) with hD
  refine ⟨x, y, D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp ha
    exact (e w).2
  · refine Finset.card_image_le.trans ?_
    calc (Finset.univ.filter (fun w : Fin S.card => (w : ℕ) < j)).card ≤ (Finset.range j).card :=
          Finset.card_le_card_of_injOn (fun w => (w : ℕ)) (fun w hw => by simpa using hw)
            (fun a _ b _ hab => Fin.ext hab)
      _ = j := Finset.card_range j
  · intro a b
    simp only [hx]
    split_ifs
    · exact hTint _ _
    · exact hzero
    · exact hzero
  · intro a b
    simp only [hy]
    split_ifs
    · exact (_root_.ReciprocityTheory.ChartRestriction.G.Sh.ptIsIntV_iff _).mpr (hTinv.2 _ _)
    · exact hzero
    · exact hzero
  · intro a b hab
    simp only [hx] at hab
    split_ifs at hab with ha hb
    · exact ⟨ha, hb⟩
    · exact absurd rfl hab
    · exact absurd rfl hab
  · intro a b hab
    simp only [hy] at hab
    split_ifs at hab with ha hb
    · exact ⟨ha, hb⟩
    · exact absurd rfl hab
    · exact absurd rfl hab
  · intro a c ha hc
    have hterm : ∀ b, x a b * y b c = if hb : b ∈ S then
        T (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) * T⁻¹ (e.symm ⟨b, hb⟩) (e.symm ⟨c, hc⟩) else 0 := by
      intro b
      simp only [hx, hy, dif_pos ha, dif_pos hc]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun b _ => hterm b),
      sum_dite_mem_eq_sum_equivFin S (fun b : S => T (e.symm ⟨a, ha⟩) (e.symm b) * T⁻¹ (e.symm b) (e.symm ⟨c, hc⟩))]
    simp only [← he, Equiv.symm_apply_apply]
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hTinv.1, Matrix.one_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
  · intro a ha haD
    set w := e.symm ⟨a, ha⟩ with hw
    have hjw : j ≤ (w : ℕ) := by
      by_contra hlt
      push_neg at hlt
      exact haD (Finset.mem_image.mpr ⟨w, by simp [hlt], by simp [hw]⟩)
    have key := hTzero w hjw
    have hp0 : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hterm : ∀ b, x a b ^ (p ^ n) • G.lc p (γ b) n = if hb : b ∈ S then
        T w (e.symm ⟨b, hb⟩) ^ (p ^ n) • G.lc p (γ b) n else 0 := by
      intro b
      simp only [hx, dif_pos ha, ← hw]
      split_ifs <;> simp [zero_pow hp0]
    rw [Finset.sum_congr rfl (fun b _ => hterm b),
      sum_dite_mem_eq_sum_equivFin S (fun b : S => T w (e.symm b) ^ (p ^ n) • G.lc p (γ b) n)]
    simp only [← he, Equiv.symm_apply_apply]
    rw [lc_sumF_eq_sum G p _ (fun u => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.isCurve_rescale (hTint w u) (hcS u))] at key
    rw [Finset.sum_congr rfl (fun u _ => lc_rescaleCurve_eq_pow_smul G p (T w u) (hcS u) n)] at key
    exact key

end GlobalTheory.RootFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafSectionEqZeroAtStageOfFilteredColimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafSection_eq_zero_at_stage_of_filtered_colimit : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  first | (exact @GlobalTheory.EtC.FilteredSections.eq_zero_at_stage_of_map_colimit_eq_zero) | (exact GlobalTheory.EtC.FilteredSections.eq_zero_at_stage_of_map_colimit_eq_zero) | (intros; apply GlobalTheory.EtC.FilteredSections.eq_zero_at_stage_of_map_colimit_eq_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicPreservesSchwartzBruhatStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ ∈ SB (Matrix α ν E), parFun c ψ χ Q (mat c p) φ ∈ SB (Matrix α ν E) := by
  first | exact @GlobalTheory.KSp.parFun_mem | exact GlobalTheory.KSp.parFun_mem | (intros; apply GlobalTheory.KSp.parFun_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfStableOfIsFractionRingStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  first | (exact @GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (exact GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (intros; apply GlobalTheory.span_eq_top_of_stable_of_isFractionRing  <;> assumption)
end

