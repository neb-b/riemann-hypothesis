module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLocalPeriodMatrix
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.PeriodLift

open GlobalTheory.LocLift GlobalTheory.ThetaValueCont Filter Topology

theorem exists_bilin_omegaStd (g : ℕ) :
    ∃ EF : LinearMap.BilinForm ℤ (Fin g ⊕ Fin g → ℤ), ∀ a b, EF a b = omegaStd a b :=
  ⟨LinearMap.mk₂ ℤ (fun x y => omegaStd x y)
    (fun x x' y => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c x y => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c x y => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring), fun _ _ => rfl⟩

theorem eq_zero_of_per_eq_zero {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef)
    {a : Fin g ⊕ Fin g → ℤ} (h : per τ a = 0) : a = 0 := by
  have h1 : (τ.map Complex.im).mulVec (fun i => (a (.inl i) : ℝ)) = 0 := by
    funext i
    have := congrArg Complex.im (congrFun h i)
    simpa [per, Matrix.mulVec, dotProduct] using this
  have h2 : (fun i => (a (.inl i) : ℝ)) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.2 hp.isUnit (h1.trans (Matrix.mulVec_zero _).symm)
  have h3 : ∀ i, a (.inl i) = 0 := fun i => by simpa using congrFun h2 i
  funext i
  rcases i with i | i
  · exact h3 i
  · simpa [per, h3, Matrix.mulVec, dotProduct] using congrFun h i

theorem perLev_of_periods (hT : ThetaUnifAV) (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {g : ℕ} (hg : P.g = g) (k : ℕ)
    (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (hon : Function.Surjective e) (hol : IsHolTo Set.univ fun z => (e z).left)
    (p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)) (hker : ∀ z, e z = 1 ↔ z ∈ p.range) (hi : Function.Injective p)
    (hs : Submodule.span ℝ (Set.range p) = ⊤) (hd : DiscreteTopology p.range)
    (hweil : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (e ((n : ℂ)⁻¹ • p a)) (e ((n : ℂ)⁻¹ • p b)) (unitOn c)) :
    IsUnit (Matrix.of fun i j => p (Pi.single (.inr j) 1) i).det ∧
      PerLev P ((Matrix.of fun i j => p (Pi.single (.inr j) 1) i)⁻¹ * Matrix.of fun i j => p (Pi.single (.inl j) 1) i) k
        fun a => e ((k : ℂ)⁻¹ • p a) := by
  subst hg
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, -, hW⟩ := hT P rig hrig
  obtain ⟨EF, hEF'⟩ := exists_bilin_omegaStd P.g
  obtain ⟨F, hF⟩ := ThetaPoint.exists_linearEquiv_lift hmul P u e hadd hon hol
    ((Set.countable_range p).mono fun z hz => (hker z).1 hz)
  have hFΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ p.range := fun z => by rw [← u.ker, hF, hker]
  have hEF : ∀ a a₂, (hermForm Hm (F (p a)) (F (p a₂))).im = EF a a₂ := fun a a₂ => by
    refine (hE ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩).symm.trans (congrArg _ ?_)
    rw [hEF']
    refine int_eq_of_exp fun k hk => ?_
    have k₁ := hW k ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have k₂ := hweil k a a₂ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    simp only [← map_smul, hF] at k₁
    exact congrArg Units.val (weilIs_unique_fieldPoint _ P.A P.L P.isLB ℂ (𝟙 _) k _ _ _ _ k₁ k₂)
  obtain ⟨Hm', h1, h2, h3⟩ : HasForm EF p := HasForm.of_comp F.toLinearMap F.injective ⟨Hm, hAH.1, hAH.2.1, hEF⟩
  obtain ⟨h, τ, hh, hinv, hτ, hsy, hp, -, hper⟩ := SiegelPeriod.exists_siegel_form _ EF _ (LinearEquiv.refl ℤ _) p Hm'
    hEF' ⟨hi, hd, hs, h1, h2, h3⟩
  simp only [LinearEquiv.refl_apply] at hinv hτ hper
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hh
  rw [← hinv, Matrix.nonsing_inv_nonsing_inv _ hdet, ← hτ]
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩
  let ψ : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofBijective h.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hh, Matrix.mulVec_surjective_iff_isUnit.2 hh⟩
  have hψ : ∀ a, ψ.symm (per τ a) = p a := fun a => by
    rw [LinearEquiv.symm_apply_eq]
    exact (hper a).symm
  obtain ⟨u', hex, hΛ, -⟩ := exists_holUnif_reparam P.A P.L P.g u (ψ.symm.trans F) (fun _ => 1)
    (differentiable_const _) (fun _ => one_ne_zero) rfl
  have hex' : ∀ (c : ℂ) a, u'.ex (c • per τ a) = e (c • p a) := fun c a => by
    rw [hex, LinearEquiv.trans_apply, hF, map_smul, hψ]
  refine ⟨rfl, hsy, hp, u', fun z => ?_, fun n a b c hn hc => ?_, fun a => (hex' _ a).symm⟩
  · rw [hΛ, LinearEquiv.trans_apply, hFΛ]
    refine exists_congr fun a => ?_
    rw [← hψ, ψ.symm.injective.eq_iff, eq_comm]
  · rw [hex', hex']
    exact hweil n a b c hn hc

theorem exists_local_period_matrix : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (Q : Out.PolAV X) (g k m : ℕ) (l : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over X) ⟶ Q.A)) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (φ₀ : P₀.A.left ⟶ Q.A.left) (τ₀ : Matrix (Fin g) (Fin g) ℂ) (lev₀ : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P₀.A)), LocallyOfFiniteType s → 0 < k → (∀ a, l a ^ k = 1) → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → PolPB P₀ Q (y b₀) φ₀ → PerLev P₀ τ₀ k lev₀ → (∀ a, (lev₀ a).left ≫ φ₀ = y b₀ ≫ (l a).left) → ∃ (B' : Set (Fin m → ℂ)) (τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ τ b₀ = τ₀ ∧ (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B') ∧ ∀ b ∈ B', ∃ (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ Q.A.left) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PolPB P Q (y b) φ ∧ PerLev P (τ b) k lev ∧ ∀ a, (lev a).left ≫ φ = y b ≫ (l a).left := by
  intro hL hT K _ σ X s Q g k m l B y b₀ P₀ φ₀ τ₀ lev₀ hft hk hl0 hB hb₀ hyσ hy ⟨hφ₀, hg₀, hL₀⟩
    ⟨hg, _, hp₀, u, hΛ, w₀, hlev₀⟩ hlev
  subst hg
  haveI : CharZero K := σ.charZero
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI := Q.isAb.proper
  obtain ⟨Φ₀, hΦ₀, hΦW₀⟩ := exists_push_iff Q P₀ hφ₀ hL₀
  have he₀ : IsExp (y b₀) fun z => Φ₀ (u.ex z) := by
    obtain ⟨rig, hrig⟩ := P₀.rigid
    obtain ⟨u₀, -, -, -, -, -, h₁, h₂, -⟩ := hT P₀ rig hrig
    obtain ⟨F, hF⟩ := ThetaPoint.exists_linearEquiv_lift hL.mulN P₀ u₀ u.ex u.ex_add u.ex_onto
      (fun U f => by simpa using u.hol U f) ((Set.countable_range (per τ₀)).mono fun z hz => by
        obtain ⟨a, ha⟩ := (hΛ z).1 ((u.ker z).1 hz)
        exact ⟨a, ha.symm⟩)
    have := (PointUnif.isExp_push hφ₀ u₀ h₁ h₂ Φ₀ hΦ₀).comp_equiv F
    simp only [hF] at this
    exact this
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, he0, hr, hol, he, hl⟩ := RelExp.exists_relative_exp K σ X s Q.A P₀.g m B y b₀
    (fun z => Φ₀ (u.ex z)) hft Q.isAb (hg₀ ▸ Q.smoothDim) hB hb₀ hyσ hy he₀
  change HasLifts B₁ y e at hl
  change ∀ b ∈ B₁, IsExp (y b) (e b) ∧ _ at he
  have hy₁ := isHolTo_mono hy hB₁ hB₁B
  let p₀ : (Fin P₀.g ⊕ Fin P₀.g → ℤ) →+ (Fin P₀.g → ℂ) := AddMonoidHom.mk' (per τ₀) (per_add τ₀)
  have hrange : Set.range p₀ = u.Λ := Set.ext fun z => by
    rw [SetLike.mem_coe, hΛ]
    exact exists_congr fun a => eq_comm
  obtain ⟨P, hP₀, hP⟩ := exists_periods latContinuation hB₁ hb₁ hy₁ hr hol he hl p₀
    ((injective_iff_map_eq_zero p₀).2 fun a ha => eq_zero_of_per_eq_zero hp₀ ha) (hrange ▸ u.full) (fun z => by
      rw [he0]
      exact (map_eq_one_iff Φ₀ Φ₀.injective).trans ((u.ker z).trans (Set.ext_iff.1 hrange z).symm))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₁.mem_nhds hb₁))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hC₁ : C ⊆ B₁ := fun b hb => (hball b hb).2
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb => ((hball b hb).1.1 x).differentiableWithinAt
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'),
      hk1 b hb]
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : Fin P₀.g ⊕ Fin P₀.g → ℤ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a a₂ : ℂ) / k) →
      Out.WeilIs Q.A Q.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (torsion_eq_and_weilIs_of_isHolTo hL X Q m k C y
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk
      (isUnit_natCast_of_over s hk) hCo hCc hC₀ (htor k a) (htor k a₂)
      fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2
        (by rw [hP₀, he0]; exact (hΦW₀ _ _ _ _).1 (w₀ k a a₂ c hk hc)) b hb
  have hleft : ∀ a b, (toUnit (Over.mk (y b)) ≫ l a).left = y b ≫ (l a).left := fun a b => by
    rw [Over.comp_left, Over.toUnit_left]; rfl
  have hsec : ∀ a, ∀ b ∈ C, toUnit _ ≫ l a = e b ((k : ℂ)⁻¹ • P b a) :=
    fun a => (torsion_eq_and_weilIs_of_isHolTo hL X Q m k C y (fun b => toUnit _ ≫ l a)
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) 1 b₀ hk (isUnit_natCast_of_over s hk) hCo hCc hC₀
      (isHolTo_congr (isHolTo_comp_hom (isHolTo_mono hy₁ hCo hC₁) (l a).left) fun b _ => hleft a b) (htor k a)
      fun b hb => ⟨by rw [← MonObj.comp_pow, hl0, MonObj.comp_one], hpow k hk a b hb⟩).1 (by
        rw [hP₀, he0]
        refine Over.OverMorphism.ext ?_
        rw [hleft, ← hlev, hlev₀]
        exact (hΦ₀ _).symm)
  have fib : ∀ b ∈ C, IsUnit (Matrix.of fun i j => P b (Pi.single (.inr j) 1) i).det ∧
      ∃ (A : Out.PolAV (Sp ℂ)) (φ : A.A.left ⟶ Q.A.left)
        (lev : (Fin P₀.g ⊕ Fin P₀.g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ A.A)), PolPB A Q (y b) φ ∧
        PerLev A ((Matrix.of fun i j => P b (Pi.single (.inr j) 1) i)⁻¹ *
          Matrix.of fun i j => P b (Pi.single (.inl j) 1) i) k lev ∧
        ∀ a, (lev a).left ≫ φ = y b ≫ (l a).left := fun b hb => by
    obtain ⟨A, φ, hφ, hgA, hm, t, ht⟩ := hL.polBaseChange _ _ (y b) Q
    have hgp : IsGrpPullback A.A Q.A (y b) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
      rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
      rfl⟩
    have hLA : LBIso A.L (Q.L.pull φ) := LBIso.symm ⟨t, ht⟩
    obtain ⟨Φ, hΦ, hΦW⟩ := exists_push_iff Q A hgp hLA
    have h₁ : ∀ z, (Φ.symm (e b z)).left ≫ φ = (e b z).left := fun z => by rw [← hΦ, Φ.apply_symm_apply]
    have hex := (he b (hC₁ hb)).1
    obtain ⟨q1, q2⟩ := perLev_of_periods hT hL.mulN A (hgA.trans hg₀.symm) k (fun z => Φ.symm (e b z))
      (fun z w => by rw [hex.1, map_mul]) (Φ.symm.surjective.comp hex.2.1)
      (ThetaPoint.isHolTo_fibre hφ _ (fun z => Over.w (Φ.symm (e b z))) (by simpa only [h₁] using hex.2.2.1)) (P b)
      (fun z => (map_eq_one_iff _ Φ.symm.injective).trans ((hball b hb).1.2.1 z)) (hball b hb).1.2.2.1
      (hball b hb).1.2.2.2.1 (hball b hb).1.2.2.2.2 fun n a a₂ c hn hc => by
        rw [hΦW, Φ.apply_symm_apply, Φ.apply_symm_apply]
        exact hwe b hb n a a₂ c hn hc
    exact ⟨q1, A, φ, _, ⟨hgp, hgA, hLA⟩, q2, fun a => by rw [h₁, ← hsec a b hb, hleft]⟩
  refine ⟨C, fun b => (Matrix.of fun i j => P b (Pi.single (.inr j) 1) i)⁻¹ *
    Matrix.of fun i j => P b (Pi.single (.inl j) 1) i, hCo, hC₀, hC₁.trans hB₁B, ?_, fun i j => ?_,
    fun b hb => (fib b hb).2⟩
  · have e1 : (Matrix.of fun i j => P b₀ (Pi.single (.inr j) 1) i) = 1 := by
      ext i j
      simp [hP₀, p₀, per, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]
    beta_reduce
    rw [e1, inv_one, Matrix.one_mul]
    ext i j
    simp [hP₀, p₀, per, Matrix.mulVec, dotProduct, Pi.single_apply]
  · have dh : ∀ i j, DifferentiableOn ℂ (fun b => (Matrix.of fun i j => P b (Pi.single (.inr j) 1) i)⁻¹ i j) C :=
      ThetaFamily.differentiableOn_left_inverse (fun i k => differentiableOn_pi.1 (hPd _) i)
        fun b hb => Matrix.nonsing_inv_mul _ (fib b hb).1
    simp only [Matrix.mul_apply]
    exact DifferentiableOn.fun_sum fun l _ => (dh i l).fun_mul (differentiableOn_pi.1 (hPd _) l)

end GlobalTheory.PeriodLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedKeyInvariantRuleCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyNormRule

def HasValue (g n : ℕ) (ka : KeyIn ℂ → ℂˣ) (a₀ : ℂ) : Prop :=
  ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c₀ : ℂ), x.P.g = g →
    charHalf x.P.g a b → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx a b c₀ →
    (ka x : ℂ) = a₀ * (Mx.det ^ 4 / c₀ ^ 8) ^ n

theorem dim_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : x'.P.g = x.P.g := by
  obtain ⟨_, _, _, hg, -⟩ := h
  exact hg

theorem HasValue.holo {g n : ℕ} {ka : KeyIn ℂ → ℂˣ} {a₀ : ℂ} (h : HasValue g n ka a₀) (a b : Fin g → ℂ)
    (hab : charHalf g a b) : ∃ U : Matrix (Fin g) (Fin g) ℂ → ℂ, Key.IsHoloSiegel g U ∧
      ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) :=
  ⟨fun _ => a₀, differentiableOn_const _, fun x hx τ hn => by
    simpa using h x τ 1 _ _ 1 hx ⟨fun i => hab.1 _, fun i => hab.2 _⟩ one_ne_zero (by simp) hn⟩

theorem exists_rule_sq (hinv : Key.Chi.InversionStatement) {g c M : ℕ}
    {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK (2 * g) c M ka) {a₀ : ℂ}
    (ha : ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₀ : ℂ), x.P.g = 2 * g → c₀ ≠ 0 → Mx.det ≠ 0 →
      NormalAt x τ Mx 0 0 c₀ → (ka ℂ x : ℂ) = a₀ * (Mx.det ^ 4 / c₀ ^ 8) ^ c) :
    ∃ kb, KaRuleK g (2 * c) M kb ∧ HasValue g (2 * c) (kb ℂ) a₀ := by
  obtain ⟨hH, hF, hU, -⟩ := hka
  have hex : ∀ (R : Type) [CommRing R] (x : KeyIn R), ∃ y, IsKeyPow y x 2 :=
    fun R _ x => exists_isKeyPow R x 2 (by norm_num)
  choose sq hsq using hex
  have hdim : ∀ {R : Type} [CommRing R] {x y : KeyIn R}, x.P.g = g → IsKeyPow y x 2 → y.P.g = 2 * g :=
    fun hx hy => hx ▸ hy.dim_eq
  have indep : ∀ (K : Type) [Field K] [CharZero K] (x y : KeyIn K), x.P.g = g → IsKeyPow y x 2 →
      (ka K (sq K x) : K) = ka K y := fun K _ _ x y hx hy =>
    hF K K (RingHom.id K) y (sq K x) (hdim hx hy)
      (keyPB_of_isKeyPow K K (RingHom.id K) x y x (sq K x) 2 (GlobalTheory.keyPB_id K x) hy (hsq K x))
  have hval : HasValue g (2 * c) (fun x => ka ℂ (sq ℂ x)) a₀ := by
    intro x τ Mx a b c₀ hx hab hc hM hn₀
    obtain ⟨n, rfl⟩ := exists_int_half hab.1
    obtain ⟨n', rfl⟩ := exists_int_half hab.2
    have hy := hsq ℂ x
    obtain ⟨e, τ', M', hd, hn⟩ :=
      normalAt_pow x _ 2 τ Mx (fun i => (n i : ℝ) / 2) (fun i => (n' i : ℝ) / 2) c₀ hy hn₀
    obtain ⟨sp, hsp, hlaw⟩ := exists_thetaLaw_zero_of_even hinv _ _ _ (even_dot_double e n n')
    obtain ⟨M'', c', hc', hq, hn'⟩ := GlobalTheory.SpMove.normalAt_spAct (sq ℂ x) τ' M' (c₀ ^ 2) sp _ _ 0 0 hsp hlaw
      (pow_ne_zero _ hc) (by simpa using hn)
    have hq' : M''.det ^ 4 / c' ^ 8 = (Mx.det ^ 4 / c₀ ^ 8) ^ 2 := by rw [hq, hd]; ring
    have hM'' : M''.det ≠ 0 := fun h => by
      rw [h] at hq'
      exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 4 hM) (pow_ne_zero 8 hc)) (by rw [← hq']; simp)
    have := ha (sq ℂ x) _ M'' c' (hdim hx hy) hc' hM'' (by simpa [Pi.zero_def] using hn')
    rw [hq', ← pow_mul] at this
    exact this
  refine ⟨fun K _ _ x => ka K (sq K x), ⟨?_, ?_, ?_, hval.holo⟩, hval⟩
  · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a Mx hP h₁ h₂
    have hy := hsq K ⟨P, hg, rig, hr, th, hth, v, hv⟩
    obtain ⟨t, ht, w, hw, M', hp, ht', hw', hd⟩ :=
      GlobalTheory.PowChange.isKeyPow_change K P hg rig hr th hth v hv th' hth' v' hv' a Mx 2 _ h₁ h₂ hy
    have key := hH K _ (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).g_pos _
      (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).rig_gen _ (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).th_ne _
      (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).basis t ht w hw (a ^ 2) M' (hdim hP hy) ht' hw'
    dsimp only
    rw [indep K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ _ hP hp]
    rw [hd, ← pow_mul, ← pow_mul] at key
    rw [show 8 * (2 * c) = 2 * (8 * c) by ring, show 4 * (2 * c) = 2 * (4 * c) by ring]
    exact key
  · intro K K' _ _ _ _ f x x' hx h
    exact hF K K' f _ _ (hdim hx (hsq K x)) (keyPB_of_isKeyPow K K' f x _ x' _ 2 h (hsq K x) (hsq K' x'))
  · intro R K _ _ _ _ _ _ _ x xK hx hM h
    obtain ⟨u, hu, hu'⟩ := hU R K (sq R x) (sq K xK) (hdim hx (hsq R x)) hM
      (keyPB_of_isKeyPow R K _ x _ xK _ 2 h (hsq R x) (hsq K xK))
    exact ⟨u, hu, fun k _ _ r xk hr hk =>
      hu' k r (sq k xk) hr (keyPB_of_isKeyPow R k r x _ xk _ 2 hk (hsq R x) (hsq k xk))⟩

theorem exists_test (hT : ThetaUnifAV) {g n : ℕ} (hg : 1 ≤ g) {ka : KeyIn ℂ → ℂˣ} {a₀ : ℂ} (h : HasValue g n ka a₀)
    {S : Type} [CommRing S] (W : WeierstrassCurve S) [W.IsElliptic] (s : S →+* ℂ) :
    ∃ (y : KeyIn S) (z : KeyIn ℂ), y.P.g = g ∧ KeyPB z y s ∧ (ka z : ℂ) = a₀ * s W.Δ ^ (g * n) := by
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.T.exists_ellipticKeyData_value_eq_discriminant hT S W
  obtain ⟨y, hy⟩ := exists_isKeyPow S x g hg
  obtain ⟨x', hx'⟩ := exists_keyPB_ring x s
  obtain ⟨z, hz⟩ := exists_isKeyPow ℂ x' g hg
  obtain ⟨⟨τ, Mx, a, b, c, hab, hc, hM, hn₀⟩, -⟩ := GlobalTheory.KeyNormalExists.exists_normalAt hT x'
  have hΔ := hxv s x' τ Mx a b c hx' hab hc hn₀
  obtain ⟨m, rfl⟩ := exists_int_half hab.1
  obtain ⟨m', rfl⟩ := exists_int_half hab.2
  obtain ⟨e, τ', M', hd, hn⟩ :=
    normalAt_pow x' z g τ Mx (fun i => (m i : ℝ) / 2) (fun i => (m' i : ℝ) / 2) c hz hn₀
  refine ⟨y, z, by rw [hy.dim_eq, hx, Nat.mul_one], keyPB_of_isKeyPow S ℂ s x y x' z g hx' hy hz, ?_⟩
  rw [h z τ' M' _ _ _ (by rw [hz.dim_eq, dim_of_keyPB hx', hx, Nat.mul_one]) ⟨fun i => hab.1 _, fun i => hab.2 _⟩
    (pow_ne_zero _ hc) (by rw [hd]; exact pow_ne_zero _ hM) hn, ← hΔ, hd, pow_mul]
  congr 2
  ring

theorem const_rat_unit (hT : ThetaUnifAV) {g n M : ℕ} (hg : 1 ≤ g)
    {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK g n M ka) {a₀ : ℂ}
    (h : HasValue g n (ka ℂ) a₀) (W : WeierstrassCurve ℤ) (hW : W.Δ ≠ 0) :
    ∃ r : ℚ, r ≠ 0 ∧ (r : ℂ) = a₀ ∧ ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
      [CharZero K] [Algebra R K] [IsFractionRing R K], IsUnit (M : R) → IsUnit (W.Δ : R) →
      ∃ w : Rˣ, algebraMap R K w = (r : K) := by
  obtain ⟨-, hF, hU, -⟩ := hka
  let S := Localization.Away W.Δ
  have hext : ∀ {T : Type} [CommRing T] (f f' : S →+* T), f = f' := fun f f' =>
    IsLocalization.ringHom_ext (Submonoid.powers W.Δ) (RingHom.ext_int _ _)
  have hlift : ∀ {T : Type} [CommRing T], IsUnit (W.Δ : T) → Nonempty (S →+* T) := fun {T} _ hu =>
    ⟨IsLocalization.Away.lift (g := Int.castRingHom T) W.Δ hu⟩
  haveI : (W.map (algebraMap ℤ S)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ]; exact IsLocalization.Away.algebraMap_isUnit W.Δ⟩
  have hQ : (W.Δ : ℚ) ≠ 0 := Int.cast_ne_zero.2 hW
  obtain ⟨i⟩ := hlift (T := ℚ) hQ.isUnit
  obtain ⟨y, z, hy, hz, hv⟩ := exists_test hT hg h (W.map (algebraMap ℤ S)) ((Rat.castHom ℂ).comp i)
  obtain ⟨yQ, hyQ⟩ := exists_keyPB_ring y i
  have hyQg : yQ.P.g = g := (dim_of_keyPB hyQ).trans hy
  rw [hF ℚ ℂ (Rat.castHom ℂ) yQ z hyQg (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yQ z _ _ hyQ hz),
    WeierstrassCurve.map_Δ, eq_intCast (algebraMap ℤ S), map_intCast, eq_ratCast] at hv
  have hC : (W.Δ : ℂ) ≠ 0 := Int.cast_ne_zero.2 hW
  refine ⟨(ka ℚ yQ : ℚ) / (W.Δ : ℚ) ^ (g * n), div_ne_zero (Units.ne_zero _) (pow_ne_zero _ hQ), ?_, ?_⟩
  · push_cast
    rw [hv, mul_div_cancel_right₀ _ (pow_ne_zero _ hC)]
  · intro R K _ _ _ _ _ _ _ hM hΔ
    obtain ⟨j⟩ := hlift hΔ
    obtain ⟨yR, hyR⟩ := exists_keyPB_ring y j
    obtain ⟨yK, hyK⟩ := exists_keyPB_ring yQ (Rat.castHom K)
    have hyK' := GlobalTheory.keyPB_trans _ _ _ y yQ yK _ _ hyQ hyK
    rw [hext ((Rat.castHom K).comp i) ((algebraMap R K).comp j)] at hyK'
    obtain ⟨u, hu, -⟩ := hU R K yR yK ((dim_of_keyPB hyR).trans hy) hM
      (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yR yK _ _ hyR hyK')
    rw [hF ℚ K _ yQ yK hyQg hyK, eq_ratCast] at hu
    have hK : (W.Δ : K) ≠ 0 := Int.cast_ne_zero.2 hW
    refine ⟨u * hΔ.unit⁻¹ ^ (g * n), ?_⟩
    have e : algebraMap R K (hΔ.unit⁻¹ : Rˣ) = (W.Δ : K)⁻¹ := by
      rw [map_units_inv, IsUnit.unit_spec, map_intCast]
    rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, e, ← hu, Rat.cast_div, Rat.cast_pow,
      Rat.cast_intCast, inv_pow, div_eq_mul_inv]

theorem rule_div {g n M : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK g n M ka)
    {r : ℚ} (hr : r ≠ 0) (h : HasValue g n (ka ℂ) r)
    (hu : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
      [CharZero K] [Algebra R K] [IsFractionRing R K], IsUnit (M : R) → ∃ w : Rˣ, algebraMap R K w = (r : K)) :
    ∃ κ, KaRuleK g n M κ ∧ HasValue g n (κ ℂ) 1 := by
  obtain ⟨hH, hF, hU, -⟩ := hka
  let κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ :=
    fun K _ _ x => ka K x * (Units.mk0 (r : K) (Rat.cast_ne_zero.2 hr))⁻¹
  have hκ : ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), (κ K x : K) = ka K x * (r : K)⁻¹ :=
    fun K _ _ x => by simp [κ]
  have hval : HasValue g n (κ ℂ) 1 := fun x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅ => by
    have : (r : ℂ) ≠ 0 := Rat.cast_ne_zero.2 hr
    rw [hκ, h x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅]
    field_simp
  refine ⟨κ, ⟨?_, ?_, ?_, hval.holo⟩, hval⟩
  · intro K _ _ P hg rig hrig th hth v hv th' hth' v' hv' a Mx hP h₁ h₂
    rw [hκ, hκ, ← _root_.mul_assoc, ← _root_.mul_assoc,
      hH K P hg rig hrig th hth v hv th' hth' v' hv' a Mx hP h₁ h₂]
  · intro K K' _ _ _ _ f x x' hx hp
    rw [hκ, hκ, hF K K' f x x' hx hp, map_mul, map_inv₀, map_ratCast]
  · intro R K _ _ _ _ _ _ _ x xK hx hM hp
    obtain ⟨u, hu₁, hu₂⟩ := hU R K x xK hx hM hp
    obtain ⟨w, hw⟩ := hu R K hM
    have hw' : (w : R) * (r.den : R) = (r.num : R) := IsFractionRing.injective R K (by
      rw [map_mul, hw, map_natCast, map_intCast]
      exact_mod_cast Rat.mul_den_eq_num r)
    refine ⟨u * w⁻¹, ?_, fun k _ _ ρ xk hρ hk => ?_⟩
    · rw [hκ, hu₁, Units.val_mul, map_mul, map_units_inv, hw]
    · have e : ρ w = (r : k) := by
        have := congrArg ρ hw'
        rw [map_mul, map_natCast, map_intCast] at this
        rw [Rat.cast_def, eq_div_iff (Nat.cast_ne_zero.2 r.den_ne_zero), this]
      rw [hκ, hu₂ k ρ xk hρ hk, Units.val_mul, map_mul, map_units_inv, e]

theorem exists_normalised_rule : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → ∀ (g c M : ℕ), 1 ≤ g → KaRule (2 * g) c M → ∃ κ, KaRuleK g (2 * c) M κ ∧ ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c₀ : ℂ), x.P.g = g → charHalf x.P.g a b → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx a b c₀ → (κ ℂ x : ℂ) = (Mx.det ^ 4 / c₀ ^ 8) ^ (2 * c) := by
  intro hL hT hinv hP hA g c M hg hR
  obtain ⟨ka, hka⟩ := GlobalTheory.KeyGalDesc.exists_kaRuleK hL.polBaseChange _ _ _ hR
  obtain ⟨a₀, ha⟩ := GlobalTheory.KeyConst.exists_const hT hinv hP hA _ c M ka (by omega) hka
  obtain ⟨kb, hkb, hv⟩ := exists_rule_sq hinv hka ha
  obtain ⟨r, hr, rfl, h₃⟩ := const_rat_unit hT hg hkb hv (WeierstrassCurve.ofJ0 ℤ)
    (by rw [WeierstrassCurve.ofJ0_Δ]; norm_num)
  obtain ⟨r', -, e, h₂⟩ := const_rat_unit hT hg hkb hv (WeierstrassCurve.ofJ1728 ℤ)
    (by rw [WeierstrassCurve.ofJ1728_Δ]; norm_num)
  obtain rfl : r' = r := Rat.cast_injective e
  obtain ⟨κ, hκ, hκv⟩ := rule_div hkb hr hv fun R K _ _ _ _ _ _ _ hM => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (3 : R) with h | h
    · refine h₃ R K hM ?_
      rw [WeierstrassCurve.ofJ0_Δ]
      convert (h.pow 3).neg using 1
      norm_num
    · refine h₂ R K hM ?_
      rw [WeierstrassCurve.ofJ1728_Δ]
      convert (h.pow 6).neg using 1
      norm_num
  exact ⟨κ, hκ, fun x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅ => by
    rw [hκv x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅, _root_.one_mul]⟩

end GlobalTheory.KeyNormRule
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SerreVanishingCubeTotalComplexExactAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.KeyKa

theorem secCube_tw_exactAt_of_veryAmpleBy : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ p, (cubeComplex (secCube f (tw M H t) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  intro R _ _ Y f H m s M hH hM hv
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hfin, hφ⟩ :=
    GlobalTheory.AbLaw.exists_finite_graded_module_secCube R Y f H m s M hH hM hv
  obtain ⟨n₀, hn⟩ := GlobalTheory.cubeComplex_grCube_exactAt_of_finite (Fin (m + 1)) R N 𝒩 hfin
  refine ⟨n₀, fun t ht p => ?_⟩
  have h01 := secCube_exactAt_zero_and_one R Y f (tw M H t) (Fin (m + 1))
    (fun i => Out.nonzeroLocus (s i)) hv.1
  match p with
  | 0 => exact h01.1
  | 1 => exact h01.2
  | p + 2 =>
    obtain ⟨φ, hb⟩ := hφ t
    have := isIso_cechComplexMap φ hb
    rw [← cechComplex_exactAt_succ_iff_cube]
    exact ((cechComplex_exactAt_succ_iff_cube _ p).2 (hn t ht (p + 2))).of_iso
      (asIso (cechComplexMap φ))

end GlobalTheory.KeyKa
end

