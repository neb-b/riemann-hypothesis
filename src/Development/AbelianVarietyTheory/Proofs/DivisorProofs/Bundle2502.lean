module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierTrivialization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormTwoSmulAndKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT


open GlobalTheory.CechPic in
theorem GlobalTheory.SymBirig.diag_form_two_smul_and_ker : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∃ E₁ : LinearMap.BilinForm ℤ La, EF = (2 : ℤ) • E₁ ∧ ∀ (k : ℕ) (a : La), 0 < k → ((∀ y, (k : ℤ) ∣ E₁ a y) ↔ ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a)) (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen) := by
  intro A _ _ g hA hg P hP h1 h2 hsym hamp e La _ Q EF hexp hQ hker hW
  obtain ⟨M, hM, hPM⟩ := _root_.GlobalTheory.BiRoot.exists_lbIso_lam_of_birigid_symm A g hA hg P hP h1 h2 hsym
  have hPM' : LBIso P (abelian₂ A M) := hPM
  obtain ⟨u, Hm, χ, hue, hF⟩ := _root_.GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp A g hA hg M hM e hexp
  obtain ⟨u', χ', hue', hF'⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u Hm χ hM hF
  have hlam : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hD := GlobalTheory.GenSpread.lbIso_pullback hPM' (lift (𝟙 A) (𝟙 A)).left
  obtain ⟨v, ψ, hve, hFv⟩ := _root_.GlobalTheory.TransportFrame.exists_holUnif_isFactorAH_of_lbIso A g _ _ u' _ χ' (pull_isLB hP _) (pull_isLB hlam _) hD hF'
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ (pull_isLB hP _) hamp g v _ ψ hFv.1 hFv.2.1 hFv.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hFv hpos
  have hmemu : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range := fun z => by rw [← u.ker, hue]; exact hker z
  have hmemv : ∀ z, z ∈ v.Λ ↔ z ∈ Q.range := fun z => by rw [← v.ker, hve, hue', hue]; exact hker z
  have hvx : ∀ z, v.ex z = e z := fun z => by rw [hve, hue', hue]
  have hNex : ∀ a b : La, ∃ n : ℤ, (hermForm Hm (Q a) (Q b)).im = n := fun a b =>
    GlobalTheory.RiemInt.im_hermForm_int hM u hF ⟨Q a, (hmemu _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hmemu _).2 ⟨b, rfl⟩⟩
  choose N hN using hNex
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ a b : La, EF a b = 2 * N a b := by
    intro a b
    have hk : ∀ k : ℕ, 0 < k → ∃ n : ℤ, ((EF a b : ℂ) - 2 * N a b) / k = n := by
      intro k hk
      let c₁ : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k)) (Complex.exp_ne_zero _)
      let c₂ : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) *
        (((Q a ⬝ᵥ ((2 : ℂ) • Hm) *ᵥ star (Q b)).im : ℝ) : ℂ) / k)) (Complex.exp_ne_zero _)
      have w1 := hW k a b c₁ hk rfl
      have w2 := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ (pull_isLB hP _) g v _ ψ hAH k (Q a) (Q b) c₂ hk
        ((hmemv _).2 ⟨a, rfl⟩) ((hmemv _).2 ⟨b, rfl⟩) rfl
      rw [hvx, hvx] at w2
      have h3 := congrArg (fun c : ℂˣ => (c : ℂ)) (_root_.GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex (Sp ℂ) A g hA hg _ (pull_isLB hP _) (𝟙 (Sp ℂ)) k _ _ c₁ c₂ w1 w2)
      simp only [c₁, c₂, Units.val_mk0] at h3
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3
      have h2 : ((Q a ⬝ᵥ ((2 : ℂ) • Hm) *ᵥ star (Q b)).im) = 2 * (N a b : ℝ) := by
        have h4 := hN a b
        unfold hermForm at h4
        have h5 : ((2 : ℂ) • Hm) *ᵥ star (Q b) = (2 : ℂ) • (Hm *ᵥ star (Q b)) := by
          rw [Matrix.smul_mulVec]
        rw [h5, dotProduct_smul, smul_eq_mul, Complex.mul_im, h4]
        simp
      rw [h2] at hn
      refine ⟨-n, mul_left_cancel₀ hpi ?_⟩
      push_cast at hn ⊢
      linear_combination (-1 : ℂ) * hn
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = (EF a b - 2 * N a b).natAbs + 1 := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ := hk K (by omega)
    have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    rw [div_eq_iff hK0] at hn
    have e2 : EF a b - 2 * N a b = (K : ℤ) * n := Int.cast_injective (α := ℂ) (by push_cast; rw [hn]; ring)
    have e3 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨n, e2⟩ (by rw [Int.natAbs_natCast]; omega)
    omega
  have hadd : ∀ a a' b, N (a + a') b = N a b + N a' b := by
    intro a a' b
    have h := key (a + a') b
    rw [map_add (f := _), LinearMap.add_apply, key, key] at h
    omega
  have hadd' : ∀ a b b', N a (b + b') = N a b + N a b' := by
    intro a b b'
    have h := key a (b + b')
    rw [map_add (f := _), key, key] at h
    omega
  have hsm : ∀ (c : ℤ) a b, N (c • a) b = c * N a b := by
    intro c a b
    have h := key (c • a) b
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul, key] at h
    have h' : 2 * (N (c • a) b - c * N a b) = 0 := by linear_combination -h
    linear_combination (mul_eq_zero.1 h').resolve_left two_ne_zero
  have hsm' : ∀ (c : ℤ) a b, N a (c • b) = c * N a b := by
    intro c a b
    have h := key a (c • b)
    rw [map_zsmul, smul_eq_mul, key] at h
    have h' : 2 * (N a (c • b) - c * N a b) = 0 := by linear_combination -h
    linear_combination (mul_eq_zero.1 h').resolve_left two_ne_zero
  refine ⟨LinearMap.mk₂ ℤ N hadd (fun c a b => by rw [hsm, smul_eq_mul]) hadd' (fun c a b => by rw [hsm', smul_eq_mul]), ?_, ?_⟩
  · ext a b
    simp [key]
  · intro k a hk
    simp only [LinearMap.mk₂_apply]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hwl : ∀ y, (((k : ℂ)⁻¹ • Q a) ⬝ᵥ Hm *ᵥ star (Q y)).im = (N a y : ℝ) / k := by
      intro y
      have h4 := hN a y
      unfold hermForm at h4
      rw [smul_dotProduct, smul_eq_mul, show ((k : ℂ)⁻¹) = (((k : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        Complex.im_ofReal_mul, h4, div_eq_inv_mul]
    have stepA : (∀ y, (k : ℤ) ∣ N a y) ↔
        ∀ l ∈ u.Λ, ∃ n : ℤ, (((k : ℂ)⁻¹ • Q a) ⬝ᵥ Hm.mulVec (star l)).im = n := by
      constructor
      · rintro h l hl
        obtain ⟨y, rfl⟩ := (hmemu l).1 hl
        obtain ⟨n, hn⟩ := h y
        exact ⟨n, by rw [hwl, hn]; push_cast; field_simp⟩
      · intro h y
        obtain ⟨n, hn⟩ := h (Q y) ((hmemu _).2 ⟨y, rfl⟩)
        rw [hwl, div_eq_iff hk0] at hn
        exact ⟨n, by exact_mod_cast (show (N a y : ℝ) = (k : ℝ) * n by rw [hn]; ring)⟩
    have stepB := (show _ ↔ _ from ⟨_root_.GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int A g hA M u Hm χ hM hF ((k : ℂ)⁻¹ • Q a), fun h => by
      obtain ⟨θ, hθ, h0, hp⟩ := GlobalTheory.TorusRM.exists_theta_of_hasGen_lam_pull g A hA M u Hm χ hM hF _ h
      exact GlobalTheory.ThetaLiouville.im_form_mem_int g u.Λ u.full Hm hF.1 _ θ hθ h0 hp⟩)
    refine stepA.trans (stepB.trans ?_)
    have c1 := GlobalTheory.RealMult.Elliptic.cls_pull_lam hM (fst A (𝟙_ (Over (Sp ℂ))))
      (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a)) (pull_isLB hlam _)
    have c2 := GlobalTheory.RealMult.Elliptic.cls_pull_lam hM (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a))
      (fst A (𝟙_ (Over (Sp ℂ)))) (pull_isLB hlam _)
    have c3 : cls (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a)) (fst A (𝟙_ (Over (Sp ℂ))))).left)
        (pull_isLB hP _) = cls ((abelian₂ A M).pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a))
          (fst A (𝟙_ (Over (Sp ℂ))))).left) (pull_isLB hlam _) := by
      rw [cls_pull hP, cls_pull hlam, (cls_eq_iff hP hlam).2 hPM']
    rw [← cls_eq_zero_iff (pull_isLB hlam _), c1, lam_comm, ← c2, ← c3, cls_eq_zero_iff, hue]
    exact Iff.rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerOfMatrixUnitsIdempotentSplit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace MatUnitIdem

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

theorem comp_prod' {X Y M : C} [MonObj M] [IsCommMonObj M] {J : Type*} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ ∏ l ∈ s, g l = ∏ l ∈ s, f ≫ g l :=
  map_prod (MonoidHom.mk ⟨fun x : Y ⟶ M => f ≫ x, MonObj.comp_one f⟩
    (fun a b => MonObj.comp_mul f a b)) g s

theorem prod_comp' {X M N : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N] {J : Type*}
    (s : Finset J) (g : J → (X ⟶ M)) (f : M ⟶ N) [IsMonHom f] :
    (∏ l ∈ s, g l) ≫ f = ∏ l ∈ s, g l ≫ f :=
  map_prod (IsMonHom.monoidHom f X) g s

end MatUnitIdem


open MatUnitIdem in
theorem matUnits_univ_of_idem : ∀ {S : Scheme.{0}} (G H : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] (E : Fin 8 → Fin 8 → (G ⟶ G)) (hE : ∀ a b, IsMonHom (E a b)) (hrel : ∀ a b c d, E a b ≫ E c d = if b = c then E a d else 1) (hsum : ∏ a, E a a = 𝟙 G) (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = E 0 0), ∀ (T : Over S) (y : Fin 8 → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ (E a 0 ≫ r) = y a := by
  intro S G H _ _ _ E hE hrel hsum i r hi hr hir hri T y
  have key : ∀ b, E b b = (E b 0 ≫ r) ≫ i ≫ E 0 b := by
    intro b
    have h1 : E b 0 ≫ E 0 b = E b b := by rw [hrel]; simp
    have h2 : E b 0 ≫ E 0 0 = E b 0 := by rw [hrel]; simp
    calc E b b = E b 0 ≫ E 0 b := h1.symm
      _ = (E b 0 ≫ E 0 0) ≫ E 0 b := by rw [h2]
      _ = (E b 0 ≫ r) ≫ i ≫ E 0 b := by rw [← hri]; simp only [Category.assoc]
  refine ⟨∏ a, y a ≫ i ≫ E 0 a, ?_, ?_⟩
  · intro b
    haveI := hE b 0
    haveI := hr
    have hx : (∏ a, y a ≫ i ≫ E 0 a) ≫ E b 0 = y b ≫ i ≫ E 0 0 := by
      rw [prod_comp', Finset.prod_eq_single b]
      · have h3 : E 0 b ≫ E b 0 = E 0 0 := by rw [hrel]; simp
        simp only [Category.assoc, h3]
      · intro a _ hab
        have h3 : E 0 a ≫ E b 0 = 1 := by rw [hrel]; simp [hab]
        simp only [Category.assoc, h3, MonObj.comp_one]
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [← Category.assoc, hx, ← hri]
    simp only [Category.assoc]
    simp only [reassoc_of% hir, hir, Category.comp_id]
  · intro z hz
    calc z = z ≫ ∏ b, E b b := by rw [hsum, Category.comp_id]
      _ = ∏ b, z ≫ E b b := comp_prod' _ _ _
      _ = ∏ b, y b ≫ i ≫ E 0 b := by
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [key, ← Category.assoc, hz]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPresentationEndomorphismsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPowerPresentation_endomorphisms_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left) (c : SiegPre g n ζ (u ≫ F.s)), SiegPB c F.univ u → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ c.A)), ∃! x : T₁ ⟶ P.A, ∀ a, x ≫ pr a = y a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∃ c' : SiegPre g n ζ ((f ≫ u) ≫ F.s), SiegPB c' F.univ (f ≫ u) ∧ ∃ pr' : Fin 8 → (P'.A ⟶ c'.A), (∀ a, IsMonHom (pr' a)) ∧ (∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a) ∧ LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) ∧ ∀ (b : P.A ⟶ P.A) (k : Fin 8 → Fin 8 → ℤ), (∀ a, b ≫ pr a = (List.ofFn fun v => pr v ^ k a v).prod) → ∃ b' : P'.A ⟶ P'.A, (∀ a, b' ≫ pr' a = (List.ofFn fun v => pr' v ^ k a v).prod) ∧ b'.left ≫ φ = φ ≫ b.left := by
  first | exact @GlobalTheory.Poinc.sharpOver_pullback_end | exact GlobalTheory.Poinc.sharpOver_pullback_end | (intros; apply GlobalTheory.Poinc.sharpOver_pullback_end <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinJetConjDirectionDiagonalExpansion
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem jet_conj_expand : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ : ℍ) (κ : Emb F → ℕ) (Ch : ℍ → ℂ), jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ i, (κ i - μ i)) * hfun (2 * s) L μ Ch τ := by
  intro hE F _ _ _ hf s N L hs hN hL τ κ Ch
  have him : 0 < (τ : ℂ).im := τ.im_pos
  have hne : τ.im ≠ 0 := τ.im_pos.ne'
  set v : ℂ := ((Real.pi / τ.im : ℝ) : ℂ) with hv
  set T : ℂ := 2 * Real.pi * Complex.I with hT
  have hT0 : T ≠ 0 := by
    simp [hT, Real.pi_ne_zero, Complex.I_ne_zero]
  have hw : v * (starRingEnd ℂ (τ : ℂ) - τ) = -T := by
    have : starRingEnd ℂ (τ : ℂ) - τ = -(2 * ((τ : ℂ).im : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp <;> ring
    rw [this, hv, hT]
    have : ((τ : ℂ).im : ℂ) = (τ.im : ℂ) := rfl
    rw [this]; push_cast
    have h0 : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
    field_simp
  set C : ℂ := T ^ 2 * Ch τ with hC
  have h1 := _root_.GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel hE F hf s N L hs hN hL τ 1 (starRingEnd ℂ (τ : ℂ) - τ) v κ him
  have h2 := _root_.GlobalTheory.HilbFam.jet_add_dir_of_hasLevel hE F hf s N L hs hN hL τ C (-T) (v - C) κ him
  rw [mul_one, hw] at h1
  have h3 : jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * v ^ (∑ i, κ i) = jet (2 * s) L κ τ (C + (v - C)) (-T) := by
    rw [add_sub_cancel, h1, mul_comm]
  rw [h3, h2, Finset.sum_div]
  refine Finset.sum_congr rfl fun μ hμ ↦ ?_
  have hle : μ ≤ κ := Finset.mem_Iic.mp hμ
  have hwt : wt (2 * s) κ = wt (2 * s) μ + 2 * ∑ i, (κ i - μ i) := by
    have : ∑ i, κ i = ∑ i, μ i + ∑ i, (κ i - μ i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ (Nat.add_sub_of_le (hle i)).symm
    simp only [wt, this]; ring
  have hsub : v / T ^ 2 - Ch τ = (v - C) / T ^ 2 := by
    rw [hC]; field_simp
  rw [hsub, hfun, ← hT, ← hC, hwt, pow_add, pow_mul, div_pow]
  field_simp

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

section Two

variable {B : Scheme.{0}} (H : Over B) [GrpObj H]
  {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {D₁ : DegData V₁ (maximalIdeal V₁)}
  {A₁ : PolAV (Sp (FractionRing V₁))} {G₁ : Over (Sp V₁)} [GrpObj G₁] [IsCommMonObj G₁]
  {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {D₂ : DegData V₂ (maximalIdeal V₂)}
  {A₂ : PolAV (Sp (FractionRing V₂))} {G₂ : Over (Sp V₂)} [GrpObj G₂] [IsCommMonObj G₂]

def Spread₂ (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left)
    (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left)
    (ρ : D₂.toPre.X →+ D₁.toPre.X) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ψ : Sp W ⟶ B)
    (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (φW : GW.left ⟶ H.left)
    (j : splitTorus (Sp W) D₁.toPre.X ⟶ GW)
    (Ω : Type) (_ : Field Ω) (α : W →+* Ω) (b₁ : V₁ →+* Ω) (hb₁ : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0)
    (GΩ : Over (Sp Ω)) (_ : GrpObj GΩ) (n : GΩ.left ⟶ GW.left) (hn : IsGrpPullback GΩ GW (spMap α) n)
    (n₁ : GΩ.left ⟶ G₁.left) (hn₁ : IsGrpPullback GΩ G₁ (spMap b₁) n₁)
    (κ : Type) (_ : Field κ) (c : W →+* κ) (b₂ : V₂ →+* κ) (hb₂ : ∀ x ∈ maximalIdeal V₂ ^ (0 + 1), b₂ x = 0)
    (Gκ : Over (Sp κ)) (_ : GrpObj Gκ) (m : Gκ.left ⟶ GW.left) (hm : IsGrpPullback Gκ GW (spMap c) m)
    (m₂ : Gκ.left ⟶ G₂.left) (hm₂ : IsGrpPullback Gκ G₂ (spMap b₂) m₂),
    IsGrpPullback GW H ψ φW ∧ IsMonHom j ∧ Function.Injective α ∧ IsLocalHom c ∧
      spMap α ≫ ψ = spMap b₁ ≫ ξ₁ ∧ spMap c ≫ ψ = spMap b₂ ≫ ξ₂ ∧ n ≫ φW = n₁ ≫ β₁ ∧ m ≫ φW = m₂ ≫ β₂ ∧
      GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb₁ hn₁ ∧
      GlobalTheory.TorusPart.pullTorus hm j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U₂.gt 0) hb₂ hm₂

def TorAt (U : Unif (maximalIdeal V₁) D₁ A₁ G₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F] (k : ℕ) (z : F)
    (c : D₁.toPre.X →+ ℤ) (x : TFK (R := V₁) F ⟶ A₁.A) : Prop :=
  ∃ (τ : Multiplicative D₁.toPre.X →* Fˣ) (q : QkPt D₁.toPre F k),
    (∀ χ, (τ (Multiplicative.ofAdd χ) : F) = z ^ c χ) ∧ q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU U.toUnifPre F k q x

end Two

section Model
open Classical

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE)

def EndOn (f : ρ.P.A ⟶ ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G) : Prop :=
  ((Over.pullback FinalForm.u₀).map f).left ≫ FinalForm.φ = FinalForm.φ ≫ Fm.left

def SecOn (a : S.Gam) (Wo : M.Z.Opens) (h : Wo.toScheme ⟶ FinalForm.G.left) : Prop :=
  h ≫ FinalForm.G.hom = Wo.ι ∧
    ∀ (x : Sp Ω ⟶ Wo.toScheme) (x' : Sp Ω ⟶ pullback ρ.P.A.hom FinalForm.u₀), x ≫ Wo.ι = M.pt → x' ≫ FinalForm.φ ≫ FinalForm.G.hom = M.pt →
      x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left → x ≫ h = x' ≫ FinalForm.φ

def Link {T : Scheme.{0}} (x : T ⟶ M.Z) (u : T ⟶ Sp S.R) (A : Over T) [GrpObj A] (φ : A.left ⟶ ρ.P.A.left)
    (gm : A.left ⟶ FinalForm.G.left) : Prop :=
  IsGrpPullback A FinalForm.G x gm ∧
    (∀ (f : ρ.P.A ⟶ ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G), EndOn FinalForm f Fm → ∀ (T' : Scheme.{0}) (p p' : T' ⟶ A.left),
      p' ≫ A.hom = p ≫ A.hom → p' ≫ φ = p ≫ φ ≫ f.left → p' ≫ gm = p ≫ gm ≫ Fm.left) ∧
    ∀ (a : S.Gam) (Wo : M.Z.Opens) (h : Wo.toScheme ⟶ FinalForm.G.left), SecOn FinalForm a Wo h →
      ∀ (T' : Scheme.{0}) (p : T' ⟶ A.left) (x' : T' ⟶ Wo.toScheme), x' ≫ Wo.ι = p ≫ A.hom ≫ x →
        p ≫ φ = p ≫ A.hom ≫ u ≫ (ρ.pt a).left → p ≫ gm = x' ≫ h

theorem Link.pull {T T₁ : Scheme.{0}} {x : T ⟶ M.Z} {u : T ⟶ Sp S.R} {A : Over T} [GrpObj A] {φ : A.left ⟶ ρ.P.A.left}
    {gm : A.left ⟶ FinalForm.G.left} (h : Link FinalForm x u A φ gm) {v : T₁ ⟶ T} {A' : Over T₁} [GrpObj A'] {w : A'.left ⟶ A.left}
    (hw : IsGrpPullback A' A v w) : Link FinalForm (v ≫ x) (v ≫ u) A' (w ≫ φ) (w ≫ gm) := by
  have e : w ≫ A.hom = A'.hom ≫ v := hw.1.w
  refine ⟨hw.comp h.1, fun f Fm hf T' p p' h₁ h₂ => ?_, fun a Wo s hs T' p x' h₁ h₂ => ?_⟩
  · have := h.2.1 f Fm hf T' (p ≫ w) (p' ≫ w) (by rw [Category.assoc, Category.assoc, e, reassoc_of% h₁])
      (by simpa only [Category.assoc] using h₂)
    simpa only [Category.assoc] using this
  · have := h.2.2 a Wo s hs T' (p ≫ w) x' (by rw [h₁, Category.assoc, reassoc_of% e])
      (by rw [Category.assoc, Category.assoc, reassoc_of% e]; simpa only [Category.assoc] using h₂)
    simpa only [Category.assoc] using this

end Model

end GlobalTheory.Poinc.Sep.Spz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowSymmetricFormBasisEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.SymMono

def elem {r : ℕ} (a b : Fin r) : LinearMap.BilinForm ℤ (Fin r → ℤ) :=
  (LinearMap.mul ℤ ℤ).compl₁₂ (LinearMap.proj a) (LinearMap.proj b)

@[simp] theorem elem_apply {r : ℕ} (a b : Fin r) (u v : Fin r → ℤ) : elem a b u v = u a * v b := rfl

def symElem {r : ℕ} (a b : Fin r) : LinearMap.BilinForm ℤ (Fin r → ℤ) :=
  (if a ≤ b then elem a b else 0) + (if a < b then elem b a else 0)

theorem symElem_symm {r : ℕ} (a b : Fin r) (u v : Fin r → ℤ) : symElem a b u v = symElem a b v u := by
  unfold symElem
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, h.le]; ring
  · simp; ring
  · simp [not_le.2 h, not_lt.2 h.le]

theorem ite_bil_apply {r : ℕ} (p : Prop) [Decidable p] (f : LinearMap.BilinForm ℤ (Fin r → ℤ)) (u v : Fin r → ℤ) :
    (if p then f else 0) u v = if p then f u v else 0 := by
  split_ifs <;> rfl

theorem sum_symElem {r : ℕ} (β : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hβ : ∀ u v, β u v = β v u) :
    β = ∑ a, ∑ b, β (Pi.single a 1) (Pi.single b 1) • symElem a b := by
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℤ (Fin r)) fun i j => ?_
  simp only [Pi.basisFun_apply, LinearMap.sum_apply, LinearMap.smul_apply, symElem,
    LinearMap.add_apply, smul_eq_mul]
  simp only [ite_bil_apply, elem_apply, Pi.single_apply, mul_add, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul]
  simp only [← ite_and]
  rw [Fintype.sum_eq_single i (fun x hx => Fintype.sum_eq_zero _ (fun y => if_neg (by tauto))),
    Fintype.sum_eq_single j (fun x hx => Fintype.sum_eq_zero _ (fun y => if_neg (by tauto))),
    Fintype.sum_eq_single j (fun y hy => if_neg (by tauto)),
    Fintype.sum_eq_single i (fun y hy => if_neg (by tauto))]
  rcases le_or_gt i j with h | h
  · simp [h, not_lt.2 h]
  · simp [h, not_le.2 h, hβ (Pi.single i 1)]

end GlobalTheory.SymMono

namespace GlobalTheory.SymMono

theorem zpow_finsum {G J : Type} [CommGroup G] (g : G) (s : Finset J) (f : J → ℤ) :
    g ^ (∑ i ∈ s, f i) = ∏ i ∈ s, g ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem symElem_mem {r : ℕ} (a b : Fin r) : symElem a b ∈ balForms (id : ℤ → ℤ) (Fin r → ℤ) :=
  mem_balForms_int.2 (symElem_symm a b)

theorem repr_self_eq_sum {r : ℕ} {I : Type} (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (i k : I) :
    ε.repr (ε i) k = ∑ a, ∑ b, (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1) (Pi.single b 1) *
      ε.repr ⟨symElem a b, symElem_mem a b⟩ k := by
  have he : ε i = ∑ a, ∑ b, (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1) (Pi.single b 1) •
      (⟨symElem a b, symElem_mem a b⟩ : balForms (id : ℤ → ℤ) (Fin r → ℤ)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact sum_symElem _ (mem_balForms_int.1 (ε i).2)
  conv_lhs => rw [he]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearEquiv.map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]

theorem eq_of_prod_zpow_eq (F : Type) [Field F] (r : ℕ) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (x y : I → F) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (h : ∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b =
      ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) : x = y := by
  classical
  set X : I → Fˣ := fun i => Units.mk0 (x i) (hx i) with hXd
  set Y : I → Fˣ := fun i => Units.mk0 (y i) (hy i) with hYd
  have hXY : ∀ a b, ∏ i, (X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) = 1 := by
    intro a b
    rw [Finset.prod_congr rfl (fun i _ => div_zpow _ _ _), Finset.prod_div_distrib, div_eq_one]
    apply Units.ext
    simpa [X, Y, Units.coe_prod] using h a b
  funext k
  have hk : X k / Y k = 1 := by
    calc X k / Y k = ∏ i, (X i / Y i) ^ (ε.repr (ε i) k) := by
          simp [Finsupp.single_apply]
      _ = ∏ i, ∏ a, ∏ b, ((X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1)
            (Pi.single b 1))) ^ (ε.repr ⟨symElem a b, symElem_mem a b⟩ k) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [repr_self_eq_sum, zpow_finsum]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [zpow_finsum]
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [zpow_mul]
      _ = ∏ a, ∏ b, (∏ i, (X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1)
            (Pi.single b 1))) ^ (ε.repr ⟨symElem a b, symElem_mem a b⟩ k) := by
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [Finset.prod_zpow]
      _ = 1 := by simp [hXY]
  simpa [X, Y] using congrArg Units.val (div_eq_one.1 hk)

end GlobalTheory.SymMono
end

