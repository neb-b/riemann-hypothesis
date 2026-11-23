module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupPeriodClassesSumConstStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_period_classes_sum_const : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {n : ℕ} (p q : Fin n → Λ →+ Hol F.V) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc) (c : GlobalTheory.CatCoh.C1 K.Oc) (β : Λ → Λ → Hol F.V), (∑ i, GlobalTheory.CatCoh.cup K.Oc (K.perCl (p i)) (K.perCl (q i))) = GlobalTheory.CatCoh.H2.mk K.Oc ℓ → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show T''.C from ℓ.1 T T' T'' φ ψ) = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)) → ∃ c' : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), GlobalTheory.CatCoh.d1 K.Oc c' T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (∑ i, p i φ.deg * q i ψ.deg - β φ.deg ψ.deg) := by
  first | exact @GlobalTheory.AnPer.cup_per_sum_const | exact GlobalTheory.AnPer.cup_per_sum_const | (intros; apply GlobalTheory.AnPer.cup_per_sum_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGaloisPairingEqPmOnePrimeDegreeStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_galois_pairing_eq_pm_one_prime_degree : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k n : ℕ, 0 < m → n = Module.finrank F F' * m → Reg (Nat.card F) n k → ∃ z : ℤ, (z = 1 ∨ z = -1) ∧ ∑ᶠ x, psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n x * star (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n x) = z * (Nat.card (GL (Fin n) F') : ℂ) := by
  first | (exact @GlobalTheory.Shin.PairPM.pairing_pm_one) | (exact GlobalTheory.Shin.PairPM.pairing_pm_one) | (intros; apply GlobalTheory.Shin.PairPM.pairing_pm_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCrystalTwoReductionsAgreeFiltration
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem crys_two_reductions : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁,
      Function.Bijective (N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀) ∧
      ∀ d : Crys κ (spMap π) A₀, crysToDR κ h d = crysToDR (divided₂ hJ) h₂ ((N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h e hA hg
  obtain ⟨-, -, -, PR, -⟩ := P
  have hπ : Function.Surjective π := by
    rw [← st.comp]; exact st.surj₁.comp st.surj
  have hb : spMap π₁ ≫ spMap ρ = spMap π ≫ spMap (RingHom.id R) := by
    rw [Cris.spMap_id, Category.comp_id, ← st.comp, Cris.spMap_comp]
  let N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁ :=
    GrpMor.of_isGrpPullback st.dpJ hb h₁
  have key : ∀ c, N.pull ((liftMor (divided₂ hJ) h₂).pull c) = (liftMor κ h).pull c := fun c ↦
    GrpMor.pull_pull (liftMor (divided₂ hJ) h₂) N (liftMor κ h) (fun _ ↦ rfl) e c
  have b := PR R A g hA hg I κ st.nil R₀ π hπ st.ker A₀ i h
  have b₂ := PR R A g hA hg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) R₁ ρ st.surj st.kerJ A₁ i₂ h₂
  refine ⟨N, ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩, fun d ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := b₂.2 x
    obtain ⟨y, rfl⟩ := b₂.2 y
    have : (liftMor κ h).pull x = (liftMor κ h).pull y := by
      rw [← key, ← key]; exact hxy
    rw [b.1 this]
  · obtain ⟨c, rfl⟩ := b.2 y
    exact ⟨_, key c⟩
  · ext c
    show d ((liftMor κ h).pull c) = d (N.pull ((liftMor (divided₂ hJ) h₂).pull c))
    rw [key]

end GlobalTheory.SqLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefectCompat
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem isLift_id_of_isLaw {O : Type} [CommRing O] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (h : IsLaw μ) : IsLift (RingHom.id O) μ := by
  refine ⟨h.const, h.unit, h.comm, ?_⟩
  simpa only [MvPowerSeries.map_id, RingHom.id_apply] using h

theorem defect_compat : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → (∀ n, ∃ s : MvPowerSeries (Fin d) O, map (algebraMap O E) s = defect c.μ n f ∧ constantCoeff s = 0) ∧ ∀ (n : ℕ) (s s' : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect c.μ (p ^ n) f → map (algebraMap O E) s' = defect c.μ (p ^ (n + 1)) f → ∃ z, c.ev (n + 1) s' = G.mulP n (c.ev n s) + (p : O) ^ n • z := by
  intro p _ O E _ _ _ hF G d c f hf
  have hD := QLogDefect.main p O O E (RingHom.id O) hF d c.μ (isLift_id_of_isLaw c.isLaw) ⊤ f hf
  have hex : ∀ n, ∃ s : MvPowerSeries (Fin d) O,
      map (algebraMap O E) s = defect c.μ n f ∧ constantCoeff s = 0 := fun n => by
    obtain ⟨s, -, hs⟩ := (_root_.GlobalTheory.series_in_ideal_iff_image O E (Fin d) ⊤ _).1.1 (hD n).1
    refine ⟨s, hs, hF.inj ?_⟩
    have h0 : ∀ i, constantCoeff (up E (nmul c.μ n) i) = 0 := fun i => by
      simp [up, (hD n).2 i]
    rw [← constantCoeff_map, hs, map_zero, defect, map_sub,
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hf.1]
    simp [hf.1]
  refine ⟨hex, fun n s s' hs hs' => ?_⟩
  obtain ⟨κ, -, hκ⟩ := (_root_.GlobalTheory.series_in_ideal_iff_image O E (Fin d ⊕ Fin d) ⊤ _).1.1 hf.2.2
  obtain ⟨s₁, hs₁, -⟩ := hex p
  have h := ((_root_.GlobalTheory.QLog.integral_cob_defect_rules O E d c.μ c.isLaw hF.inj f κ hκ).2.2 p s₁ hs₁).2 (p ^ n) s s' hs
    (by rw [← pow_succ]; exact hs')
  haveI := hF.complete
  refine ⟨c.ev (n + 1) s₁, ?_⟩
  rw [h, map_add (f := _), map_smul, (_root_.GlobalTheory.QLog.Chart.ev_nmul_pow p O G d c n).2.2, Nat.cast_pow]
  exact add_comm _ _

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDividedPowerFiltrationSuccLe
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DerFil

theorem fil_succ_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) :
    fil δ (N + 1) ≤ fil δ N :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, by omega, h3⟩

theorem prod_mem_fil {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ)
    (l : List (ℕ × B)) (hl : ∀ p ∈ l, p.2 ∈ J) (hN : N ≤ (l.map Prod.fst).sum) :
    (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ fil δ N :=
  Ideal.subset_span ⟨l, hl, hN, rfl⟩

theorem smul_deriv_prod_mem {R B M : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J)
    (D : Derivation R B M) (N₀ : Submodule B M)
    (hD : ∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) (N : ℕ) :
    ∀ (l : List (ℕ × B)), (∀ p ∈ l, p.2 ∈ J) → ∀ (l' : List (ℕ × B)), (∀ p ∈ l', p.2 ∈ J) →
      N + 1 ≤ (l'.map Prod.fst).sum + (l.map Prod.fst).sum →
      (l'.map fun p ↦ δ.dpow p.1 p.2).prod • D ((l.map fun p ↦ δ.dpow p.1 p.2).prod) ∈
        fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  intro l
  induction l with
  | nil => intro _ l' _ _; simp
  | cons p l ih =>
    intro hl l' hl' hs
    have hp : p.2 ∈ J := hl p (by simp)
    have hl2 : ∀ q ∈ l, q.2 ∈ J := fun q hq ↦ hl q (by simp [hq])
    simp only [List.map_cons, List.prod_cons, List.sum_cons] at hs ⊢
    rw [Derivation.leibniz, smul_add, smul_smul, smul_smul]
    refine add_mem ?_ ?_
    · have hl3 : ∀ q ∈ p :: l', q.2 ∈ J := by
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact hl' q hq
      have := ih hl2 (p :: l') hl3 (by simp only [List.map_cons, List.sum_cons]; omega)
      simpa only [List.map_cons, List.prod_cons, mul_comm] using this
    · rcases p with ⟨k, x⟩
      cases k with
      | zero => simp [δ.dpow_zero hp]
      | succ m =>
        have h := hD m x hp
        set c := (l'.map fun p ↦ δ.dpow p.1 p.2).prod * (l.map fun p ↦ δ.dpow p.1 p.2).prod
        have e : c • D (δ.dpow (m + 1) x) =
            c • (D (δ.dpow (m + 1) x) - δ.dpow m x • D x) + (c * δ.dpow m x) • D x := by
          rw [smul_sub, smul_smul, sub_add_cancel]
        rw [e]
        refine add_mem (Submodule.mem_sup_right (N₀.smul_mem _ h)) (Submodule.mem_sup_left ?_)
        refine Submodule.smul_mem_smul ?_ Submodule.mem_top
        have hm := prod_mem_fil δ N (l' ++ (m, x) :: l)
          (by
            intro q hq
            rcases List.mem_append.1 hq with hq | hq
            · exact hl' q hq
            · rcases List.mem_cons.1 hq with rfl | hq
              · exact hp
              · exact hl2 q hq)
          (by simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hs ⊢; omega)
        simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons] at hm
        convert hm using 1
        simp only [c]; ring

end GlobalTheory.DerFil


open GlobalTheory.DerFil in
theorem GlobalTheory.DerFil.deriv_fil_succ_le : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J) (D : Derivation R B M)
    (N₀ : Submodule B M), (∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) →
    ∀ N, ∀ x ∈ fil δ (N + 1), D x ∈ fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  intro R B M _ _ _ _ _ _ _ J δ D N₀ hD N x hx
  induction hx using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨l, hl, hs, rfl⟩ := hb
    simpa using smul_deriv_prod_mem J δ D N₀ hD N l hl [] (by simp) (by simpa using hs)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x hx ih =>
    rw [smul_eq_mul, Derivation.leibniz]
    exact add_mem (Submodule.smul_mem _ _ ih)
      (Submodule.mem_sup_left (Submodule.smul_mem_smul (fil_succ_le δ N hx) Submodule.mem_top))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealTopFormalLogConstOne
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem dIn_top_formalLog_map : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q]
    (σ : Type) (g : MvPowerSeries σ B), constantCoeff g = 1 →
      DIn (⊤ : Ideal B) (formalLog (map (algebraMap B Q) g)) := by
  intro B Q _ _ _ _ σ g hg α i
  classical
  obtain ⟨u, hu⟩ : IsUnit g := isUnit_iff_constantCoeff.mpr (by rw [hg]; exact isUnit_one)
  set φ := algebraMap B Q
  have hG : constantCoeff (map φ g) = 1 := by simp [hg]
  have hd : pderiv (R := Q) i (formalLog (map φ g)) = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g) := by
    have h1 := mul_pderiv_formalLog hG i
    rw [pderiv_map] at h1
    have h2 : map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g = 1 := by
      rw [← map_mul, ← hu, Units.inv_mul, map_one]
    calc pderiv (R := Q) i (formalLog (map φ g))
        = (map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g) * pderiv (R := Q) i (formalLog (map φ g)) := by
          rw [h2, one_mul]
      _ = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g) := by
          rw [mul_assoc, h1, map_mul]
  by_cases hα : α i = 0
  · exact ⟨0, Submodule.mem_top, by simp [hα]⟩
  · refine ⟨coeff (α - Finsupp.single i 1) ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g),
      Submodule.mem_top, ?_⟩
    rw [natCast_mul_coeff_of_pderiv_eq hd hα, coeff_map]

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginNoeth
section
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnitsNoeth

theorem exists_unit_of_mem_map_comap {A' B' : Type} [CommRing A'] [CommRing B'] [IsDomain B']
    [IsLocalRing B'] (f : A' →+* B') (b : B')
    (h : b ∈ ((Ideal.span {b}).comap f).map f) : ∃ (d : A') (w : B'ˣ), b = f d * w := by
  by_cases hb : b = 0
  · exact ⟨0, 1, by simp [hb]⟩
  by_contra hne
  push_neg at hne
  have hle : ((Ideal.span {b}).comap f).map f ≤ Ideal.span {b} * maximalIdeal B' := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hd
    obtain ⟨z, hz⟩ := hd
    rw [Ideal.mem_comap, hz]
    by_cases hzu : IsUnit z
    · exact absurd (by rw [hz]; exact (Units.mul_inv_cancel_right b hzu.unit).symm) (hne d hzu.unit⁻¹)
    · exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self b) ((mem_maximalIdeal z).2 hzu)
  obtain ⟨m, hm, hbm⟩ := (Ideal.mem_span_singleton_mul).1 (hle h)
  have h1 : m = 1 := by
    have : b * (m - 1) = 0 := by rw [mul_sub, hbm, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hb
    · exact sub_eq_zero.1 h0
  exact (mem_maximalIdeal m).1 hm (h1 ▸ isUnit_one)

theorem divConst_origin_noeth : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 →
      bA * cA = algebraMap A (Localization.AtPrime QA) sA →
    ∃ (a : T) (w : Oˣ), jA bA = algebraMap T O a * (w : O) := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ QA _ hQA jA hjA
    bA cA sA hs hbc
  obtain ⟨A', _, _, _, _, B', _, _, _, _, _, _, _, ι, α, β, γ, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin T O hT P φ hφ hsh hP A i hi hil EA QA hQA jA hjA sA hs
  have hbc' : β bA * β cA = algebraMap A' B' (ι sA) := by
    have e := congrArg (fun g => g sA) h1
    simp only [RingHom.comp_apply] at e
    rw [e, ← hbc, map_mul]
  have hmem := GlobalTheory.T.divisor_descent_flat_normal_domains A' B' (ι sA) h4 h5 (β bA) (β cA) hbc'
  obtain ⟨d, w, hdw⟩ := exists_unit_of_mem_map_comap (algebraMap A' B') (β bA) hmem
  have e3 := congrArg (fun g => g d) h3
  simp only [RingHom.comp_apply] at e3
  refine ⟨α d, Units.map γ.toMonoidHom w, ?_⟩
  rw [← h2, RingHom.comp_apply, hdw, map_mul, e3]
  rfl

end GlobalTheory.VertUnitsNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltrationIdealLeMapOfIsDPMorphism
section
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem fil_le_map_fil : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C]
    (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → J' = J.map f →
    ∀ N, fil δ' N ≤ (fil δ N).map f := by
  intro B _ J δ C _ J' δ' f hf hJ N
  subst hJ
  have hmul : ∀ {m n : ℕ} {a b : C}, a ∈ (fil δ m).map f → b ∈ (fil δ n).map f →
      a * b ∈ (fil δ (m + n)).map f := by
    intro m n a b ha hb
    have : (fil δ m).map f * (fil δ n).map f ≤ (fil δ (m + n)).map f := by
      rw [← Ideal.map_mul]
      exact Ideal.map_mono (Ideal.mul_le.2 fun x hx y hy ↦ ExpBij.mul_mem_dpFil δ hx hy)
    exact this (Ideal.mul_mem_mul ha hb)
  have hzero : ∀ c : C, c ∈ (fil δ 0).map f := by
    intro c
    rw [fil_zero_eq_top, Ideal.map_top]
    trivial
  have hdp : ∀ y ∈ J.map f, ∀ n, δ'.dpow n y ∈ (fil δ n).map f := by
    intro y hy
    change y ∈ Ideal.span (f '' (J : Set B)) at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro n
      rw [hf.dpow_comp a ha]
      exact Ideal.mem_map_of_mem _ (ExpBij.dpow_mem_dpFil δ ha n)
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hzero _
      · rw [δ'.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ'.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hmul (ihx k.1) (ihy k.2)
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ'.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J.map f) →
      (l.map fun p ↦ δ'.dpow p.1 p.2).prod ∈ (fil δ (l.map Prod.fst).sum).map f := by
    intro l hl
    induction l with
    | nil => exact hzero _
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hmul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq]))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact Ideal.map_mono (ExpBij.dpFil_anti δ h2) (hprod l h1)

end GlobalTheory.PDA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCompSectionOfProperSmoothNilpotentRigidity
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Rigidity

theorem spMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hs : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) :
    Function.Surjective (spMap π) := by
  have h := _root_.range_comap_of_surjective R₀ π hs
  have h2 : PrimeSpectrum.zeroLocus (RingHom.ker π : Set R) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    obtain ⟨n, hn⟩ := hn
    refine ⟨n, ?_⟩
    have : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact (Submodule.mem_bot R).1 this
  rw [h2, Set.range_eq_univ] at h
  exact h

theorem eq_comp_section : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (P X : Over (Sp R)) (P₀ : Over (Sp R₀)) (l : P₀.left ⟶ P.left), IsPullback l P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f : P ⟶ X) (s₀ : Sp R₀ ⟶ X.left), l ≫ f.left = P₀.hom ≫ s₀ →
    f.left = P.hom ≫ ε ≫ f.left := by
  intro R R₀ _ _ π hs hn P X P₀ l hpb hsm hpr hgc ε hε f s₀ hf
  have := hsm
  have := hpr
  have : GeometricallyIntegral P.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.hom hsm hgc
  have hsurj : ∀ V : (Sp R).Opens, Function.Surjective (P.hom.app V).hom := fun V => by
    have := GlobalFunctions.isIso_app FlatFibreInjective.injective_baseChange
      exists_noetherian_model_of_smooth P.hom V
    exact (ConcreteCategory.bijective_of_isIso (P.hom.app V)).2
  have hloc : ∀ t : Sp R, ∃ V : (Sp R).Opens, t ∈ V ∧
      (P.hom ⁻¹ᵁ V).ι ≫ f.left = (P.hom ⁻¹ᵁ V).ι ≫ P.hom ≫ ε ≫ f.left := by
    intro t
    obtain ⟨t₀, ht₀⟩ := spMap_surjective π hs hn t
    refine local_rigidity _ _ _ P.hom ε f.left hε inferInstance hsurj t (s₀ t₀) ?_
    intro x hx
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := P.hom) (g := spMap π) x t₀
      (hx.trans ht₀.symm)
    have e₁ : l (hpb.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
    have e₂ : P₀.hom (hpb.isoPullback.inv z) = t₀ := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz₂]
    rw [← e₁, ← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply, e₂]
  choose V hV hfg using hloc
  have hc : TopologicalSpace.IsOpenCover (fun t => P.hom ⁻¹ᵁ V t) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    exact fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨P.hom x, hV (P.hom x)⟩
  exact (P.left.openCoverOfIsOpenCover _ hc).hom_ext _ _ fun t => hfg t

end GlobalTheory.Rigidity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivLiftResiduePadicAlgClStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algEquiv_lift_residue_padicAlgCl : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) (φ : GlobalTheory.ZJ.kb l ≃+* GlobalTheory.ZJ.kb l), (∀ x : GlobalTheory.ZJ.OO l, (x : PadicAlgCl l) ∈ L → φ (IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) = IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ x y : GlobalTheory.ZJ.OO l, IsLocalRing.residue (GlobalTheory.ZJ.OO l) y = φ (IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) → ‖g (x : PadicAlgCl l) - y‖ < 1 := by
  first | exact @GlobalTheory.ZJ.exists_algEquiv_lift_residue | exact GlobalTheory.ZJ.exists_algEquiv_lift_residue | (intros; apply GlobalTheory.ZJ.exists_algEquiv_lift_residue <;> assumption)
end

