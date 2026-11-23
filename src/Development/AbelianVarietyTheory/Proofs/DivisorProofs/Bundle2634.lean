module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBoundedHomogeneousIntFormFamilies
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.Count

theorem abs_intCast_le_iff (c : ℤ) {R : ℝ} (hR : 0 ≤ R) :
    |(c : ℝ)| ≤ R ↔ c ∈ Finset.Icc (-(⌊R⌋₊ : ℤ)) (⌊R⌋₊ : ℤ) := by
  rw [Finset.mem_Icc, ← abs_le, ← Int.cast_abs, ← Int.le_floor, Int.natCast_floor_eq_floor hR]

theorem coeff_sum_monomial {D q : ℕ} [Fintype {α : Fin (D + 1) →₀ ℕ // α.degree = q}]
    (g : {α : Fin (D + 1) →₀ ℕ // α.degree = q} → ℤ) (β : Fin (D + 1) →₀ ℕ) :
    AddMonoidAlgebra.coeff (∑ a, monomial a.1 (g a)) β = if h : β.degree = q then g ⟨β, h⟩ else 0 := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨β, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Subtype.ext e)
    · simp
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg]
    rintro rfl
    exact h a.2

theorem coeff_eq_zero_of_isHomogeneous {D q : ℕ} {P : MvPolynomial (Fin (D + 1)) ℤ}
    (hP : P.IsHomogeneous q) {β : Fin (D + 1) →₀ ℕ} (hβ : β.degree ≠ q) : AddMonoidAlgebra.coeff P β = 0 := by
  by_contra hc
  exact hβ (by rw [Finsupp.degree_eq_weight_one]; exact hP hc)

end GlobalTheory.HSAmp.Count

open GlobalTheory.HSAmp.Count in
theorem GlobalTheory.HSAmp.card_bounded_forms : ∀ (D q δ : ℕ) (R : ℝ), 0 ≤ R → {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}.Finite ∧ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}.ncard = (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ∧ Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D ∧ Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) = (q + D).choose D ∧ Module.Finite ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) := by
  intro D q δ R hR
  classical
  have hAcard : Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D := by
    rw [GlobalTheory.natCard_degree_eq, Fintype.card_fin, show q + (D + 1) - 1 = q + D by omega,
      Nat.choose_symm_add]
  haveI : Finite {α : Fin (D + 1) →₀ ℕ // α.degree = q} := (Finsupp.finite_of_degree_eq q).to_subtype
  letI : Fintype {α : Fin (D + 1) →₀ ℕ // α.degree = q} := Fintype.ofFinite _
  set S := {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧
    ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R} with hS
  let F : S → (Fin δ → {α : Fin (D + 1) →₀ ℕ // α.degree = q} →
      Finset.Icc (-(⌊R⌋₊ : ℤ)) (⌊R⌋₊ : ℤ)) :=
    fun T i a => ⟨AddMonoidAlgebra.coeff (T.1 i) a.1, (abs_intCast_le_iff _ hR).1 (T.2.2 i a.1)⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨T, hT⟩ ⟨T', hT'⟩ h
      apply Subtype.ext
      funext i
      ext β
      by_cases hβ : β.degree = q
      · have := congrArg Subtype.val (congrFun (congrFun h i) ⟨β, hβ⟩)
        simpa [F] using this
      · rw [coeff_eq_zero_of_isHomogeneous (hT.1 i) hβ, coeff_eq_zero_of_isHomogeneous (hT'.1 i) hβ]
    · intro f
      refine ⟨⟨fun i => ∑ a, monomial a.1 ((f i a : ℤ)), fun i => ?_, fun i β => ?_⟩, ?_⟩
      · exact IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_monomial _ a.2
      · rw [coeff_sum_monomial]
        split_ifs with h
        · exact (abs_intCast_le_iff _ hR).2 (f i ⟨β, h⟩).2
        · simpa using hR
      · funext i a
        apply Subtype.ext
        change AddMonoidAlgebra.coeff (∑ b, monomial b.1 (f i b : ℤ)) a.1 = (f i a : ℤ)
        rw [coeff_sum_monomial, dif_pos a.2]
  let e := Equiv.ofBijective F hF
  have hfin : S.Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)
  refine ⟨hfin, ?_, hAcard, ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_fun, hAcard,
      Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc, Nat.card_eq_fintype_card,
      Fintype.card_fin, ← pow_mul, mul_comm]
    congr 1
    omega
  · rw [homogeneousSubmodule_eq_finsupp_supported]
    exact (Module.finrank_eq_nat_card_basis
      (basisRestrictSupport ℤ {d : Fin (D + 1) →₀ ℕ | d.degree = q})).trans hAcard
  · rw [homogeneousSubmodule_eq_finsupp_supported]
    haveI : Finite {d : Fin (D + 1) →₀ ℕ | d.degree = q} := (Finsupp.finite_of_degree_eq q).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport ℤ {d : Fin (D + 1) →₀ ℕ | d.degree = q})
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamClassEqZeroOfPeriodsZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
open Opposite GlobalTheory.CatCoh

namespace GlobalTheory.CechPer

theorem eq_zero_of_isPer_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ x, IsPer u.ex u.Λ x 0 → x = 0 := by
  intro A _ g L u hA x hx
  obtain ⟨c, h, rfl, ⟨hd, hc, hω⟩, hp⟩ := hx
  obtain ⟨hopen, -, -, -, -, hmono, -, hloc, hres, halg, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  have vsub : ∀ (U : A.left.Opens) (a b : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (a - b : Sec (str A) U) z = val u.ex U a z - val u.ex U b z := by
    intro U a b z hz
    obtain ⟨e, he⟩ := halg U z hz
    exact (he (a - b : Sec (str A) U)).trans ((map_sub e a b).trans (congrArg₂ (· - ·) (he a).symm (he b).symm))
  have hreg : ∀ U V : A.left.affineOpens, IsReg u.ex (U.1 ⊓ V.1) (h U - h V) := by
    intro U V
    apply _root_.GlobalTheory.CechPer.isReg_of_locally A g L u hA
    intro z hz
    obtain ⟨W, hW, hzW⟩ := hloc _ z hz
    have hWU : W ≤ U := (le_inf_iff.1 hW).1
    have hWV : W ≤ V := (le_inf_iff.1 hW).2
    refine ⟨W.1, hW, hzW, (c.1.1 (op V) (op W) (homOfLE hWV).op - c.1.1 (op U) (op W) (homOfLE hWU).op :
      Sec (str A) W.1), fun y hy ↦ ?_⟩
    have e0 := vsub W.1 (c.1.1 (op V) (op W) (homOfLE hWV).op) (c.1.1 (op U) (op W) (homOfLE hWU).op) y hy
    have e1 := hc U W (homOfLE hWU).op y hy
    have e2 := hc V W (homOfLE hWV).op y hy
    refine Eq.trans ?_ e0.symm
    rw [Pi.sub_apply]
    linear_combination e2 - e1
  have hb := _root_.GlobalTheory.CechPer.isReg_of_periodic_of_isReg_sub A g L u hA A.left.affineOpens (fun U ↦ U.1) h
    (iSup_affineOpens_eq_top A.left) hd (fun U l z hz ↦ by simpa using hp U l z hz) hreg
  choose b hb using hb
  let b' : ∀ U : A.left.affineOpens, Sec (str A) U.1 := b
  refine (Hyp1.mk_eq_zero (F := OAff (str A))).2 ⟨fun T ↦ b' T.unop, Tot1.ext (fun T T' a ↦ ?_) (fun T ↦ ?_)⟩
  · obtain ⟨U⟩ := T
    obtain ⟨V⟩ := T'
    have hVU : V.1 ≤ U.1 := leOfHom a.unop
    have hz0 := _root_.GlobalTheory.ValInj.eq_zero_of_val_eq_zero A g L u hA V.1
      ((b' V - Sec.res (str A) hVU (b' U) - c.1.1 (op U) (op V) a : Sec (str A) V.1)) (fun z hz ↦ by
        have e0 := vsub V.1 (b' V - Sec.res (str A) hVU (b' U)) (c.1.1 (op U) (op V) a) z hz
        have e1 := vsub V.1 (b' V) (Sec.res (str A) hVU (b' U)) z hz
        have e2 := hres U.1 V.1 hVU (b' U) z hz
        have e3 : h V z = val u.ex V.1 (b' V) z := hb V z hz
        have e4 : h U z = val u.ex U.1 (b' U) z := hb U z (hmono _ _ hVU hz)
        have e5 := hc U V a z hz
        refine e0.trans ?_
        linear_combination e1 - e2 - e3 + e4 + e5)
    exact sub_eq_zero.1 (show (b' V - Sec.res (str A) hVU (b' U) - c.1.1 (op U) (op V) a : Sec (str A) V.1) = 0 from hz0)
  · obtain ⟨U⟩ := T
    change KaehlerDifferential.D ℂ (Sec (str A) U.1) (b' U) = c.1.2 (op U)
    apply sub_eq_zero.1
    apply _root_.GlobalTheory.form_eq_zero_of_evForm_eq_zero A g L u hA U
    intro z hz
    rw [map_sub, (_root_.GlobalTheory.CechPer.evForm_rules A g L u U.1 z hz).2.2 (b' U), ← hω U z hz, sub_eq_zero]
    refine (Filter.EventuallyEq.fderiv_eq ?_).symm
    filter_upwards [(hopen U.1).mem_nhds hz] with y hy
    exact hb U y hy

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowEqMumfordFormula
section
set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowPull

theorem tri_succ (n : ℤ) : tri (n + 1) = tri n + (n + 1) := by
  unfold tri
  have : (n + 1) * (n + 1) + (n + 1) = n * n + n + (n + 1) * 2 := by ring
  rw [this, Int.add_mul_ediv_right _ _ two_ne_zero]

theorem tri_neg (n : ℤ) : tri (-n) = tri n - n := by
  unfold tri
  have : n * n + n = -n * -n + -n + n * 2 := by ring
  rw [this, Int.add_mul_ediv_right _ _ two_ne_zero]
  ring

theorem eq_of_rec {M : Type*} [AddCommGroup M] (f : ℤ → M) (a l : M) (h0 : f 0 = 0)
    (hs : ∀ n, f (n + 1) = f n + a + n • l) (n : ℤ) : f n = n • a + tri (-n) • l := by
  have step : ∀ n : ℤ, tri (-(n + 1)) = tri (-n) + n := fun n => by
    rw [tri_neg, tri_neg, tri_succ]; ring
  induction n using Int.induction_on with
  | zero => simp [h0, tri]
  | succ n ih => rw [hs, ih, step]; module
  | pred n ih =>
    have h := hs (-(n : ℤ) - 1)
    have h' := step (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h h'
    rw [ih, h'] at h
    rw [eq_sub_of_add_eq (eq_sub_of_add_eq h.symm)]
    module


open GlobalTheory.CechPic in
theorem pull_zpow : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (z : T ⟶ A) (n : ℤ), GlobalTheory.CechPic.pull (z ^ n).left (GlobalTheory.CechPic.cls L hL) = tri n • GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) + tri (-n) • GlobalTheory.CechPic.pull (z⁻¹).left (GlobalTheory.CechPic.cls L hL) := by
  intro K _ A _ hA L hL T z n
  have := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen :=
    GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have h1 : pull (1 : T ⟶ A).left (cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local, map_zero]
  let φ : (T ⟶ A) →* Multiplicative (Pic T.left) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (lam (cls L hL) x z)) fun x y => by
      rw [lam_mul_left hL hΘ, ofAdd_add]
  have hz : ∀ m : ℤ, lam (cls L hL) (z ^ m) z = m • lam (cls L hL) z z := fun m =>
    congrArg Multiplicative.toAdd (map_zpow φ z m)
  have key := eq_of_rec (fun m => pull (z ^ m).left (cls L hL)) (pull z.left (cls L hL)) (lam (cls L hL) z z)
    (by rw [zpow_zero, h1]) (fun m => by
      rw [← hz, zpow_add_one, lam, h1]; abel)
  have k1 := key (-1)
  have t1 : tri (- -1) = 1 := by decide
  rw [zpow_neg_one, t1] at k1
  rw [key n, k1, tri_neg]
  module

end GlobalTheory.PowPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowMulMixedSplit
section
set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeMixed

open GlobalTheory.CechPic

theorem lam_zpow_left {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℤ) :
    lam (cls L hL) (x ^ n) z = n • lam (cls L hL) x z := by
  cases n with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, natCast_zsmul]
    exact lam_pow_left hL hΘ x z k
  | negSucc k =>
    have h := lam_mul_left hL hΘ (x ^ (k + 1)) (x ^ (k + 1))⁻¹ z
    rw [mul_inv_cancel, lam_one_left, lam_pow_left hL hΘ] at h
    rw [zpow_negSucc, negSucc_zsmul]
    exact eq_neg_of_add_eq_zero_right h.symm

theorem lam_zpow_zpow {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y : T ⟶ G) (m n : ℤ) :
    lam (cls L hL) (x ^ m) (y ^ n) = (m * n) • lam (cls L hL) x y := by
  rw [lam_zpow_left hL hΘ, lam_comm, lam_zpow_left hL hΘ, lam_comm, smul_smul]

theorem pull_one_eq_zero {K : Type} [Field K] {A T : Over (Sp K)} [GrpObj A] (c : CechPic.Pic A.left) :
    CechPic.pull (1 : T ⟶ A).left c = 0 := by
  change CechPic.pull ((toUnit T).left ≫ (η : 𝟙_ (Over (Sp K)) ⟶ A).left) c = 0
  rw [pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) _ c, map_zero]

theorem mixed_mul : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (x y : T ⟶ A) (m n a b : ℤ), a • GlobalTheory.CechPic.pull (x ^ m * y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m * y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL) = (a • GlobalTheory.CechPic.pull (x ^ m).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + (a • GlobalTheory.CechPic.pull (y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + ((a + b) * (m * n)) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
  intro K _ A _ hA L hL T x y m n a b
  have : IsCommMonObj A := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen := GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have key : ∀ (c : CechPic.Pic A.left) (u v : T ⟶ A),
      CechPic.pull (u * v).left c = CechPic.pull u.left c + CechPic.pull v.left c + lam c u v := by
    intro c u v
    unfold lam
    rw [pull_one_eq_zero]
    abel
  rw [mul_inv, key, key, ← zpow_neg, ← zpow_neg, lam_zpow_zpow hL hΘ, lam_zpow_zpow hL hΘ, neg_mul_neg]
  module

end GlobalTheory.CubeMixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreUniqueUpToIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GFibUniq

theorem isPrimitiveRoot_map {o : Type} [CommRing o] [IsDomain o] {ζ : o} {L : ℕ} (hL : 0 < L)
    (hζ : IsPrimitiveRoot ζ L) (hu : IsUnit (L : o)) (κ : Type) [Field κ] (a : o →+* κ) : IsPrimitiveRoot (a ζ) L := by
  haveI : NeZero (L : κ) := ⟨by simpa using (hu.map a).ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have hr := (hζ.isRoot_cyclotomic hL).map (f := a)
  simpa [Polynomial.map_cyclotomic] using hr

theorem latAt_unique : ∀ (o Ω : Type) [CommRing o] [IsDomain o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → IsPrimitiveRoot (ζ : o) L → IsUnit (L : o) → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (m : I → X →+ X) (c : T → X →+ ZMod L) (m' : I → X' →+ X') (c' : T → X' →+ ZMod L) (w : M.Z), LatAt f gγ ζ L m c w → LatAt f gγ ζ L m' c' w → ∃ e : X ≃+ X', (∀ i x, e (m i x) = m' i (e x)) ∧ ∀ t x, c' t (e x) = c t x := by
  intro o Ω _ _ _ _ M G _ _ hG I T f gγ ζ L hL hζ hu X X' _ _ _ _ _ _ m c m' c' w h h'
  haveI : IsSeparated G.hom := hG.separated
  exact LatAt.unique hL (fun κ _ a => isPrimitiveRoot_map hL hζ hu κ a) h h'

end GlobalTheory.UPoinc.GFibUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevels
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem chart_square_presents : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), Presents k c.x₂ c.nil₂ ∧ ∀ z : ∀ n, G.A n ⊗[k] G.A n,
      (∀ n, pullbackTwo (G.res n) (z (n + 1)) = z n) → ∃! s, ∀ n, c.ev₂ n s = z n := by
  intro p k _ d G c
  have ht := fun n => _root_.GlobalTheory.evA_tensor_presents k (Fin d) (Fin d) (G.A n) (G.A n) (c.x n) (c.nil n) (c.x n)
    (c.nil n) (c.nil₂ n) (c.presents.1 n) (c.presents.1 n)
  refine ⟨⟨fun n => (ht n).1, fun N => ?_⟩, fun z hz => ?_⟩
  · obtain ⟨n, hn⟩ := c.presents.2 N
    exact ⟨n, (ht n).2 N hn hn⟩
  · let r : ∀ n, G.A n.succ ⊗[k] G.A n.succ →ₐ[k] G.A n ⊗[k] G.A n := fun n =>
      Algebra.TensorProduct.map (G.res n : G.A (n + 1) →ₐ[k] G.A n)
        (G.res n : G.A (n + 1) →ₐ[k] G.A n)
    have hr : ∀ n t, r n t = pullbackTwo (G.res n) t := fun n t => by
      induction t with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a b => rfl
    refine GlobalTheory.T.existsUnique_powerSeries_of_compatible_system k (Fin d ⊕ Fin d) (fun n => G.A n ⊗[k] G.A n) c.x₂ c.nil₂ r
      (fun n i => ?_) ⟨fun n => (ht n).1, fun N => ?_⟩ z (fun n => by rw [hr]; exact hz n)
    · rw [hr]
      cases i with
      | inl i => simp [Chart.x₂, c.res]
      | inr i => simp [Chart.x₂, c.res]
    · obtain ⟨n, hn⟩ := c.presents.2 N
      exact ⟨n, (ht n).2 N hn hn⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormPowerIntegralHermLineBundlePow
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp GlobalTheory.ChartGlue GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.ChPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X}

theorem cHess_zero' (v : ReciprocityTheory.L2DbarEstimates.V D) :
    ReciprocityTheory.L2DbarEstimates.cHess D (fun _ => ((0 : ℝ) : ℂ)) v = 0 := by
  have h := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul isOpen_univ (p := fun _ => (0 : ℝ)) (q := fun _ => (0 : ℝ))
    contDiffOn_const contDiffOn_const 1 (Set.mem_univ v)
  simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h
  simpa using h

theorem hess_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (n : ℕ) {j : PUnit → B.ι} (hj : y ∈ ptsIn p σ (B.U (j PUnit.unit))) :
    c.hess (φ.pow n) j y = (n : ℂ) • c.hess φ (j PUnit.unit) y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (j PUnit.unit)))
  have hm := mem_over c.e hy hj
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (p := fun _ => (0 : ℝ)) contDiffOn_const
    (contDiffOn_chart (hφ (j PUnit.unit)) c) (n : ℝ) hm
  rw [cHess_zero', zero_add] at e
  simp only [zero_add, Complex.ofReal_natCast] at e
  refine Eq.trans ?_ e
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((φ.pow n).φ j (c.e.symm v) : ℝ) : ℂ)) (c.e y) = _
  congr 1
  funext v
  simp [Weight.pow, Weight.zpow_φ]

theorem chernDens_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (n : ℕ) : c.chernDens (φ.pow n) y = (n : ℝ) ^ D * c.chernDens φ y := by
  have hj := (mem_pow_iff (n := (n : ℤ))).1 (mem_pick (φ.pow n).isLB y)
  rw [c.chernDens_eq hφ hy hj, AlgChart.chernDens, hess_pow hφ c hy n hj, Matrix.det_smul, Fintype.card_fin,
    ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

theorem chernPart_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (n : ℕ) (ε : ℤˣ) :
    (φ.pow n).chernPart D ε = ENNReal.ofReal ((n : ℝ) ^ D) • φ.chernPart D ε := by
  have h := GlobalTheory.ChernScale.glueMeas_restrict_eq (fun c : AlgChart p σ D => c.e)
    (ρ := fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens (φ.pow n) y))
    (ρ' := fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) ENNReal.ofReal_ne_top MeasurableSet.univ
    fun c y hy _ => by
      rw [chernDens_pow hφ c hy n, mul_left_comm, ENNReal.ofReal_mul (by positivity)]
  rw [Weight.chernPart, Weight.chernPart]
  simpa only [Measure.restrict_univ] using h

end GlobalTheory.HSAmp.ChPow

namespace GlobalTheory.HSAmp


open ChPow in
theorem chInt_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (n : ℕ) (w : ∀ σ, CxPts p σ → ℝ), chInt (L.pow n) D w = (n : ℝ) ^ D * chInt L D w := by
  intro k _ X _ p D _ L n w
  rw [chInt, chInt, mul_finsum]
  refine finsum_congr fun σ => ?_
  show ((L.φ σ).pow n).chernInt D Set.univ (w σ) = _
  rw [Weight.chernInt, Weight.chernInt, chernPart_pow (L.cInf σ), chernPart_pow (L.cInf σ), Measure.restrict_smul,
    Measure.restrict_smul, integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul, smul_eq_mul, mul_sub]

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularConnectionEqEsymmGraded
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem chernFld_ldPart_eq_esymm_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ j p, chernFld (atlas X σ) (fun y z => ldPart (gramAt E H τ y z)) j p = aeval (fun i => grF E H ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j) := by
  intro F _ σ X ι _ m E H hH τ j p
  set A := (E.nonempty (under p.pt)).choose with hAdef
  have hA : A ∈ E.S (under p.pt) := (E.nonempty (under p.pt)).choose_spec
  have hev := ((_root_.GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt F σ X ι m m E H hH p.pt A hA τ).2 p.1.1 p.2)
  change ∀ᶠ v in 𝓝 p.crd, MContDiffAt ∞ (fun u => H A (p.ch.symm u) τ) v ∧ (H A (p.ch.symm v) τ).PosDef at hev
  have h0 := hev.self_of_nhds
  have hs := _root_.GlobalTheory.ChernCalc.ldPart_grD_smooth X.dim (m τ) (fun u => H A (p.ch.symm u) τ) p.crd h0.1 h0.2
  have hp0 := _root_.GlobalTheory.ChernCalc.ldPart_posDef_spec (m τ) _ h0.2
  show chernAt (fun v => ldPart (H A (p.ch.symm v) τ)) p.crd j = _
  refine (_root_.GlobalTheory.ChernTri.chernAt_tri X.dim (m τ) (fun v => ldPart (H A (p.ch.symm v) τ))
    (fun i v => grD (H A (p.ch.symm v) τ) i) p.crd hs.1 (fun i => (hp0.2.1 i).1) ?_ j).trans rfl
  filter_upwards [hev] with x hx
  have hpx := _root_.GlobalTheory.ChernCalc.ldPart_posDef_spec (m τ) _ hx.2
  exact ⟨hpx.2.2.1, fun i => (hpx.2.1 i).2⟩

end GlobalTheory.ChernCalc
end

