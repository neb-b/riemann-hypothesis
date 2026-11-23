module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesInjective
section
open scoped TensorProduct Matrix Classical

noncomputable section

namespace GlobalTheory.CCRFock

open MvPolynomial

theorem polMap_index_injective (W Λ : Type) [Fintype W] :
    Function.Injective (fun f : W → (Λ →₀ ℕ) => ∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) := by
  have key : ∀ (f : W → (Λ →₀ ℕ)) (w : W) (l : Λ),
      (∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) (w, l) = f w l := by
    intro f w l
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single w]
    · exact Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective w) _ _
    · intro v _ hv
      apply Finsupp.mapDomain_notin_range
      rintro ⟨x, hx⟩
      exact hv (congrArg Prod.fst hx)
    · intro h
      exact absurd (Finset.mem_univ w) h
  intro f g h
  funext w
  ext l
  rw [← key f w l, ← key g w l]
  exact congrArg (fun F : (W × Λ) →₀ ℕ => F (w, l)) h

theorem polMap_tprod_monomial (W Λ : Type) [Fintype W] [DecidableEq W] (f : W → (Λ →₀ ℕ)) :
    polMap W Λ (PiTensorProduct.tprod ℂ (fun w => (monomial (f w) (1 : ℂ) : MvPolynomial Λ ℂ))) =
      monomial (∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) 1 := by
  rw [monomial_sum_one]
  simp only [polMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, rename_monomial]

theorem polMap_injective (W Λ : Type) [Fintype W] [DecidableEq W] :
    Function.Injective (polMap W Λ) := by
  let B := Basis.piTensorProduct (fun _ : W => basisMonomials Λ ℂ)
  have hli : LinearIndependent ℂ (polMap W Λ ∘ B) := by
    have h := (basisMonomials (W × Λ) ℂ).linearIndependent.comp _ (polMap_index_injective W Λ)
    have e : polMap W Λ ∘ B = (basisMonomials (W × Λ) ℂ) ∘
        (fun f : W → (Λ →₀ ℕ) => ∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) := by
      funext f
      simp only [Function.comp, B, Basis.piTensorProduct_apply, coe_basisMonomials]
      exact polMap_tprod_monomial W Λ f
    rw [e]
    exact h
  have h1 : polMap W Λ ∘ₗ Finsupp.linearCombination ℂ B = Finsupp.linearCombination ℂ (polMap W Λ ∘ B) := by
    ext f
    simp
  intro x y hxy
  apply B.repr.injective
  apply hli
  rw [← h1]
  simp only [LinearMap.comp_apply, Module.Basis.linearCombination_repr, hxy]

end GlobalTheory.CCRFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishTorsion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem theta_nonvanish_coset (k : Type) [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (N : ℕ) (hN : 2 ≤ N) (hNk : (N : k) ≠ 0)
    (θ : LB.Sec (LPow P.A P.L 1 (baseOver (Spec (CommRingCat.of k)))))
    (hθ : SecM.ofSec P.A θ ≠ 0) (a : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) :
    ∃ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, x ^ N = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Spec (CommRingCat.of k))).left) (K := Fin 1)
          (fun _ => (a * x).left) (fun _ => 1))) (v : Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 θ (a * x) τ v ∧ v ≠ 0 :=
  abelianSchemeLaws_all.1.goodPt k P N hN hNk θ hθ a

theorem theta_nonvanish_torsion (k : Type) [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (N : ℕ) (hN : 2 ≤ N) (hNk : (N : k) ≠ 0)
    (θ : LB.Sec (LPow P.A P.L 1 (baseOver (Spec (CommRingCat.of k)))))
    (hθ : SecM.ofSec P.A θ ≠ 0) :
    ∃ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, x ^ N = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Spec (CommRingCat.of k))).left) (K := Fin 1)
          (fun _ => x.left) (fun _ => 1))) (v : Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 θ x τ v ∧ v ≠ 0 := by
  obtain ⟨x, hx, rest⟩ := theta_nonvanish_coset k P N hN hNk θ hθ 1
  exact ⟨1 * x, by rw [_root_.one_mul]; exact hx, rest⟩

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemValueEqRootMulThetaConstant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.EvRoot
open GlobalTheory.ThetaCompare

variable {S : Scheme.{0}}

private theorem val_powFrame_divisor {S : Scheme.{0}} (P : PolAV S) {T : Over S} (h : T ⟶ P.A)
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (k : ℤ)
    (y : T.left) (J : (T.left ⟶ P.A.left) → P.L.ι) :
    val (powFrame P.A P.L h τ k) (𝟙 _) y J = val τ (𝟙 _) y J ^ k := by
  unfold powFrame val gm
  split_ifs
  · exact map_zpow _ _ _
  · exact (one_zpow k).symm

private theorem val_rigPow' {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ S) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι) :
    val (rigPow P.A P.L rig k) r z J = val rig r z J ^ k := by
  unfold rigPow val gm
  split_ifs
  · exact map_zpow _ _ _
  · exact (one_zpow k).symm


open CommPairing in
theorem exists_root_stalk_pull (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M m : ℕ}
    {rig : LB.Gen (P.L.pull (eSec P.A))}
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1])}
    (hα : α.IsGen)
    (hn : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left)
      (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))))
    {h w : T ⟶ P.A} (hw : w = h ^ m) {τ τ'} (hτ : IsTorsFrame P rig M h τ)
    (hτ' : IsTorsFrame P rig M w τ') {th : LB.Sec (LPow P.A P.L 1 T)} {s : LB.Sec (LPow P.A P.L N T)}
    (hs : IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) N 1 α th s) {v v' : Γ(T.left, ⊤)}
    (hv : IsValueAt P.A P.L N s h (powFrame P.A P.L h τ N) v) (hv' : IsValueAt P.A P.L 1 th w τ' v') (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (M ^ 2) = 1 ∧ gs (𝟙 _) y ⊤ v = ξ.val * gs (𝟙 _) y ⊤ v' := by
  have hL : P.L.IsLB := P.isLB
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt hL y
  have e1 := sval_twist hs (ptSecT P.A h).left hJ
  rw [pt_mulT, ← hw, sval_valueAt hv hJ, sval_valueAt hv' hJ] at e1
  refine ⟨val α (ptSecT P.A h).left y J * val τ' (𝟙 _) y J * (val (powFrame P.A P.L h τ N) (𝟙 _) y J)⁻¹, ?_, ?_⟩
  · unfold IsTorsFrame at hτ hτ'
    obtain ⟨hhM, -, β, hβ, hnβ, hcβ⟩ := hτ
    obtain ⟨-, -, β', hβ', hnβ', hcβ'⟩ := hτ'
    have eτ : val τ (𝟙 _) y J ^ ((M : ℤ) ^ 2) = val β h.left y J * val rig T.hom y J := by
      rw [← val_powFrame_divisor, val_corr hJ hcβ (𝟙 _), val_mul hJ, val_pull hJ, val_rigT rig 1 hJ, zpow_one,
        Category.id_comp]
    have eτ' : val τ' (𝟙 _) y J ^ ((M : ℤ) ^ 2) = val β' w.left y J * val rig T.hom y J := by
      rw [← val_powFrame_divisor, val_corr hJ hcβ' (𝟙 _), val_mul hJ, val_pull hJ, val_rigT rig 1 hJ, zpow_one,
        Category.id_comp]
    have orbitMap_conj_smul_one : val α (ptSecT P.A 1).left y J = val rig T.hom y J ^ (N : ℤ) * val rig T.hom y J ^ (-1 : ℤ) := by
      have := val_corr hJ hn (𝟙 _)
      rw [val_pull hJ, val_mul hJ, val_rigT rig _ hJ, val_rigT rig _ hJ, Category.id_comp] at this
      exact this
    have eB1 : val β (T.hom ≫ eSec P.A) y J = val rig T.hom y J ^ ((M : ℤ) ^ 2) * (val rig T.hom y J)⁻¹ := by
      have := val_corr hJ hnβ T.hom
      rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow'] at this
      exact this
    have eB1' : val β' (T.hom ≫ eSec P.A) y J = val rig T.hom y J ^ ((M : ℤ) ^ 2) * (val rig T.hom y J)⁻¹ := by
      have := val_corr hJ hnβ' T.hom
      rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow'] at this
      exact this
    have rA := Reg.two (L := P.L) (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
    have rB := Reg.two (L := P.L) (y := y) (J := J) (LB.pullGen P.L _ _ β (snd T P.A).left)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen P.L _ _ β hβ _) (snd T P.A) (snd T P.A ^ M)
      (by simp)
      (by show (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
          rw [← Over.comp_left, GlobalTheory.DivisibleHom.comp_mulA])
    have rB' := Reg.two (L := P.L) (y := y) (J := J) (LB.pullGen P.L _ _ β' (snd T P.A).left)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen P.L _ _ β' hβ' _) (snd T P.A) (snd T P.A ^ M)
      (by simp)
      (by show (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
          rw [← Over.comp_left, GlobalTheory.DivisibleHom.comp_mulA])
    have rF := ((rA.pow hJ (M ^ 2)).mul hJ (rB'.pull hJ (snd T P.A ^ m))).mul hJ
      (((rB.pow hJ N).inv).mul hJ ((rA.pull hJ (snd T P.A ^ M)).inv))
    have hmM : (snd T P.A ^ m) ^ M = (snd T P.A ^ M) ^ m := by
      rw [← pow_mul, ← pow_mul, _root_.mul_comm]
    have hF := Reg.const hG P.isAb hL hJ rF (by
      intro U _ hh
      simp only [CartesianMonoidalCategory.lift_snd, GlobalTheory.SymLiftOdd.comp_pow', hmM]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv, ofMul_one]
      simp only [← natCast_zsmul]
      push_cast
      module) h 1
    simp only [val_pull hJ, ← Over.comp_left, pt_snd, GlobalTheory.SymLiftOdd.comp_pow', one_pow, hhM, ← hw,
      GlobalTheory.UU.one_left] at hF
    rw [val_powFrame_divisor]
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul hF
    have f2 := congrArg Additive.ofMul eτ
    have f3 := congrArg Additive.ofMul eτ'
    have f4 := congrArg Additive.ofMul orbitMap_conj_smul_one
    have f5 := congrArg Additive.ofMul eB1
    have f6 := congrArg Additive.ofMul eB1'
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv, ofMul_one, ← natCast_zsmul] at f1 f2 f3 f4 f5 f6 ⊢
    push_cast at f1 f2 f3 f4 f5 f6 ⊢
    linear_combination (norm := module) f1 + f3 - (N : ℤ) • f2 + ((M : ℤ) ^ 2) • f4 + f6 - (N : ℤ) • f5
  · have e2 : gs (𝟙 _) y ⊤ v = gs (𝟙 _) y ⊤ v * (val (powFrame P.A P.L h τ N) (𝟙 _) y J).val *
        ((val (powFrame P.A P.L h τ N) (𝟙 _) y J)⁻¹ : (T.left.presheaf.stalk y)ˣ).val := by
      rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    rw [e2, e1]
    simp only [Units.val_mul]
    ring

private theorem real_pt_nsmul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    ∀ (c : ℕ) (b : S.Gam), ρ.pt (c • b) = ρ.pt b ^ c := by
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  intro c b
  induction c with
  | zero => rw [zero_smul, h0, pow_zero]
  | succ c ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]

private theorem exists_injective_stalk_hom_gs_eq {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) :
    ∃ (y : (baseOver (Sp S.R)).left) (φ : S.R →+* (baseOver (Sp S.R)).left.presheaf.stalk y),
      Function.Injective φ ∧ ∀ a : S.R, gs (𝟙 _) y ⊤ (fn a) = φ a := by
  have hI : IsIntegral (baseOver (Sp S.R)).left := by
    first
    | infer_instance
    | (show IsIntegral (Spec (CommRingCat.of S.R)); infer_instance)
  refine ⟨genericPoint _, (((baseOver (Sp S.R)).left.presheaf.germ ⊤ (genericPoint _) trivial).hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom, ?_, ?_⟩
  · intro a b h
    have h1 := AlgebraicGeometry.germ_injective_of_isIntegral (baseOver (Sp S.R)).left (U := ⊤) (genericPoint _) trivial
    exact (Scheme.ΓSpecIso (CommRingCat.of S.R)).commRingCatIsoToRingEquiv.symm.injective (h1 h)
  · intro a
    unfold gs
    rw [dite_eq_left (show _ ∈ (⊤ : (baseOver (Sp S.R)).left.Opens) from trivial)]
    rfl

private theorem exists_rootOfUnity_mul_of_pow_eq_pow {K : Type} [Field K] (a b : K) (n : ℕ) (hn : 0 < n) (h : a ^ n = b ^ n) :
    ∃ u : K, u ^ n = 1 ∧ a = u * b := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_pow hn.ne'] at h
    exact ⟨1, one_pow n, by rw [pow_eq_zero_iff hn.ne'] at h; simp [h]⟩
  · refine ⟨a / b, ?_, (div_mul_cancel₀ a hb).symm⟩
    rw [div_pow, h, div_self (pow_ne_zero n hb)]

theorem ev_eq_root_mul_th : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (x : S.Gam) (j : S.J), ∃ (y : S.Gam) (u : Ω) (k : ℕ), 0 < k ∧ u ^ k = 1 ∧ S.ev x j = u * S.th y := by
  intro o Ω _ _ _ _ S ρ x j
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨a, e, ha⟩ := ρ.orbit j
  have hpt : ∀ (c : ℕ) (b : S.Gam), ρ.pt (c • b) = ρ.pt b ^ c := real_pt_nsmul ρ
  have hpt0 : ρ.pt 0 = 1 := by simpa using hpt 0 0
  have hzero : ∀ b : S.Gam, (S.r * S.N) • b = 0 := by
    intro b; funext i; simp [nsmul_eq_mul]
  have hN : Odd S.N := by rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hx : ρ.pt (S.r • a) ^ S.N = 1 := by
    rw [← hpt, smul_smul, show S.N * S.r = 1 * (S.r * S.N) by ring, mul_smul, hzero, smul_zero, hpt0]
  have hM : ρ.pt (S.r • a) ^ (S.r * S.N) = 1 := by
    rw [← hpt, smul_smul, show S.r * S.N * S.r = S.r * (S.r * S.N) by ring, mul_smul, hzero, smul_zero, hpt0]
  have hev : ∀ (i : S.J) (b : S.Gam), IsValueAt ρ.P.A ρ.P.L (S.N : ℤ) (ρ.s i) (ρ.pt b)
      (powFrame ρ.P.A ρ.P.L (ρ.pt b) (ρ.fr b) S.N) (fn (⟨S.ev b i, S.ev_mem b i⟩ : S.R)) := by
    intro i b; have := ρ.ev_val i; unfold IsEvT at this; exact this b
  obtain ⟨y, φ, hφi, hφ⟩ := exists_injective_stalk_hom_gs_eq S
  obtain ⟨ξ1, hξ1, H1⟩ := GlobalTheory.ZH.EvCrd.exists_root_stalk hG ρ.P (T := baseOver (Sp S.R)) (N := S.N)
    (M := S.r * S.N) hN (rig := ρ.rig) (x := ρ.pt (S.r • a)) (h := ρ.pt x) (w := ρ.pt (S.r • a + x)) hx hM
    (ρ.pt_add _ _) (θ := ρ.U a) (ρ.U_sym a) (ρ.fr_tors x) (ρ.fr_tors (S.r • a + x)) y
  have E1 := H1 S.J ρ.s (ρ.s ρ.i₀) (fun l => fn (algebraMap o S.R (S.ρ a l ρ.i₀)))
    (fun l => fn (⟨S.ev x l, S.ev_mem x l⟩ : S.R)) (fn (⟨S.ev (S.r • a + x) ρ.i₀, S.ev_mem _ _⟩ : S.R))
    (ρ.U_act a ρ.i₀) (fun l => hev l x) (hev ρ.i₀ _)
  obtain ⟨ξ2, hξ2, H2⟩ := exists_root_stalk_pull hG ρ.P (T := baseOver (Sp S.R)) (N := S.N) (M := S.r * S.N)
    (m := ρ.n ^ ρ.k) (rig := ρ.rig) (α := ρ.α) ρ.α_gen ρ.α_norm (h := ρ.pt (S.r • a + x))
    (w := ρ.pt ((ρ.n ^ ρ.k) • (S.r • a + x))) (hpt _ _) (ρ.fr_tors _) (ρ.fr_tors _) (th := ρ.th₁)
    (s := ρ.s ρ.i₀) ρ.s_zero (hev ρ.i₀ _) (ρ.th_val _) y
  simp only [hφ] at E1 H2
  rw [Finset.sum_eq_single j (fun l _ hl => by rw [ha l, if_neg hl]; simp)
    (fun hj => absurd (Finset.mem_univ j) hj)] at E1
  rw [ha j, if_pos rfl] at E1
  set K := (S.r * S.N) ^ 2 with hK
  have hKpos : 0 < K := by
    have := S.r_pos; have := S.N_ge; positivity
  have hu1 := congrArg Units.val hξ1
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hu1
  have hu2 := congrArg Units.val hξ2
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hu2
  have hR : (algebraMap o S.R (S.ζ ^ e) * ⟨S.ev x j, S.ev_mem x j⟩) ^ K =
      (⟨S.th ((ρ.n ^ ρ.k) • (S.r • a + x)), S.th_mem _⟩ : S.R) ^ K := by
    apply hφi
    rw [map_pow, map_mul, E1, H2, map_pow, mul_pow, mul_pow, hu1, hu2, _root_.one_mul, _root_.one_mul]
  have hz : (algebraMap o Ω S.ζ) ^ K = 1 := by rw [hK, ← map_pow, S.prim.pow_eq_one, map_one]
  have hΩ := congrArg (fun z : S.R => (z : Ω)) hR
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at hΩ
  rw [mul_pow, map_pow, ← pow_mul, _root_.mul_comm e, pow_mul, hz, one_pow, _root_.one_mul] at hΩ
  obtain ⟨u, hu, hux⟩ := exists_rootOfUnity_mul_of_pow_eq_pow _ _ K hKpos hΩ
  exact ⟨_, u, K, hKpos, hu, hux⟩

end GlobalTheory.ZH.EvRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchBasicOpenMorphismUnique
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchUniq

section
variable (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

theorem appTop_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (c : Γ(Sp (TrivSqZeroExt R M), ⊤))
    (h1 : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom c = 0)
    (h2 : (spMap β).appTop.hom c = 0) : c = 0 := by
  have n1 := congrArg (fun k => k.hom c)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom))
  have n2 := congrArg (fun k => k.hom c) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom β))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n1 n2
  have h1' : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom)).appTop.hom c = 0 := h1
  have h2' : (Spec.map (CommRingCat.ofHom β)).appTop.hom c = 0 := h2
  rw [h1', map_zero] at n1
  rw [h2', map_zero] at n2
  set c' := (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).hom.hom c with hc'
  have e1 : TrivSqZeroExt.fst c' = 0 := n1.symm
  have e2 : TrivSqZeroExt.snd c' = 0 := by
    have : β c' = TrivSqZeroExt.inl (algebraMap R B (TrivSqZeroExt.fst c')) + TrivSqZeroExt.inr (TrivSqZeroExt.snd c') := by
      conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq c']
      rw [map_add (f := _), hβ.1, hβ.2]; rfl
    have := congrArg TrivSqZeroExt.snd this
    rw [← n2] at this
    simpa using this.symm
  have hc0 : c' = 0 := TrivSqZeroExt.ext e1 e2
  have : c = (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv.hom c' := by
    rw [hc']; simp
  rw [this, hc0, map_zero]

theorem exists_pow_of_appLE_eq_zero {A : Type} [CommRing A] (s a : Γ(Sp A, ⊤)) (n : ℕ)
    {Y : Scheme.{0}} [IsAffine Y] (f : Y ⟶ Sp A)
    (hf : (f.appLE _ _ le_rfl).hom
      (IsLocalization.mk' Γ(Sp A, (Sp A).basicOpen s) a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)) = 0) :
    ∃ N : ℕ, f.appTop.hom (s ^ N * a) = 0 := by
  have hspec := IsLocalization.mk'_spec Γ(Sp A, (Sp A).basicOpen s) a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)
  have h3 : (f.appLE _ _ le_rfl).hom (algebraMap Γ(Sp A, ⊤) Γ(Sp A, (Sp A).basicOpen s) a) = 0 := by
    rw [← hspec, map_mul, hf, zero_mul]
  have h4 : (f.appLE ⊤ (f ⁻¹ᵁ (Sp A).basicOpen s) (by simp)).hom a = 0 := by
    rw [← h3]
    show _ = (((Sp A).presheaf.map (homOfLE le_top).op) ≫ f.appLE _ _ le_rfl).hom a
    rw [Scheme.Hom.map_appLE]
  have hle : Y.basicOpen (f.appTop.hom s) ≤ f ⁻¹ᵁ (Sp A).basicOpen s := (Scheme.preimage_basicOpen_top f s).ge
  have h6 : (f.appLE ⊤ (Y.basicOpen (f.appTop.hom s)) (by simp)).hom a = 0 := by
    rw [← Scheme.Hom.appLE_map (i := (homOfLE hle).op), CommRingCat.comp_apply, h4, map_zero]
    simp
  have h5 : f.appTop.hom a |_ (Y.basicOpen (f.appTop.hom s)) = 0 := h6
  obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y (isAffineOpen_top Y) _ _ h5
  exact ⟨N, by rw [map_mul, map_pow]; exact hN⟩

theorem appLE_basicOpen_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (t : Γ(Sp (TrivSqZeroExt R M), (Sp (TrivSqZeroExt R M)).basicOpen s))
    (h1 : ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appLE _ _ le_rfl).hom t = 0)
    (h2 : ((spMap β).appLE _ _ le_rfl).hom t = 0) : t = 0 := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) t
  obtain ⟨N₁, hN₁⟩ := exists_pow_of_appLE_eq_zero s a n _ h1
  obtain ⟨N₂, hN₂⟩ := exists_pow_of_appLE_eq_zero s a n _ h2
  have hc : s ^ (N₁ + N₂) * a = 0 := by
    apply appTop_joint_inj R B M β hβ
    · rw [pow_add, mul_comm (s ^ N₁), _root_.mul_assoc, map_mul, hN₁, mul_zero]
    · rw [pow_add, _root_.mul_assoc, map_mul, hN₂, mul_zero]
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨_, N₁ + N₂, rfl⟩, hc⟩

theorem resLE_appTop_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (a b : Γ(((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme, ⊤))
    (h1 : ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl).appTop.hom a =
      ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl).appTop.hom b)
    (h2 : ((spMap β).resLE _ _ le_rfl).appTop.hom a = ((spMap β).resLE _ _ le_rfl).appTop.hom b) : a = b := by
  have conv : ∀ {Y : Scheme.{0}} (f : Y ⟶ Sp (TrivSqZeroExt R M)) (c : Γ(((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme, ⊤)),
      (f.resLE ((Sp (TrivSqZeroExt R M)).basicOpen s) (f ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) le_rfl).appTop.hom c =
        (f ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.inv.hom
          ((f.appLE _ _ le_rfl).hom (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom c)) := by
    intro Y f c
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    rfl
  rw [conv, conv] at h1 h2
  replace h1 := congrArg (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
    (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom h1
  replace h2 := congrArg (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom h2
  simp only [Iso.inv_hom_id_apply] at h1 h2
  have hz := appLE_basicOpen_joint_inj R B M β hβ s
    (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom a - ((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom b)
    (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self])
  exact (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.commRingCatIsoToRingEquiv).injective (sub_eq_zero.mp hz)

end

theorem uniq : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (V : (Sp (TrivSqZeroExt R M)).Opens) (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)), V = (Sp (TrivSqZeroExt R M)).basicOpen s → ∀ (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1 → ∀ g₁ g₂ : V.toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₁ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₂ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap β).resLE V _ le_rfl ≫ g₁ = (spMap β).resLE V _ le_rfl ≫ g₂ → g₁ = g₂ := by
  intro R _ B M _ _ _ _ _ _ _ _ _ _ β hβ X x V s hV U hU g₁ g₂ h₁ h₂ h₃
  subst hV
  have hrange : ∀ g : ((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme ⟶ X,
      (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g =
        (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ x →
      Set.range g ⊆ Set.range U.1.ι := by
    rintro g hg _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨w, hw⟩ := GlobalTheory.Pinch.spMap_fst_surjective R M p.1
    have hwV : w ∈ spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s := by
      rw [Scheme.Hom.mem_preimage, hw]; exact p.2
    have hp : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ⟨w, hwV⟩ = p :=
      Subtype.ext (by rw [Scheme.Hom.coe_resLE_apply]; exact hw)
    rw [← hp]
    change ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g) ⟨w, hwV⟩ ∈ (U.1 : Set X)
    rw [hg]
    exact hU hwV
  haveI : IsAffine U.1.toScheme := U.2
  have f₁ := IsOpenImmersion.lift_fac U.1.ι g₁ (hrange g₁ h₁)
  have f₂ := IsOpenImmersion.lift_fac U.1.ι g₂ (hrange g₂ h₂)
  have ei : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) =
      (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, f₁, f₂, h₁, h₂]
  have ej : (spMap β).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) =
      (spMap β).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, f₁, f₂, h₃]
  have hl : IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) = IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    apply ext_of_isAffine
    ext u
    apply resLE_appTop_joint_inj R B M β hβ s
    · have := congrArg (fun φ => φ.appTop.hom u) ei
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using this
    · have := congrArg (fun φ => φ.appTop.hom u) ej
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using this
  rw [← f₁, ← f₂, hl]

end GlobalTheory.PinchUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAtStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_eq_norm_completionTensor_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∀ u : Fv F v, Valued.v u = 1 →
      ∃ z : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) u = z * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ z := by
  first | exact @GlobalTheory.InertUnitNorm.unit_eq_mul_conj | exact GlobalTheory.InertUnitNorm.unit_eq_mul_conj | (intros; apply GlobalTheory.InertUnitNorm.unit_eq_mul_conj <;> assumption)
end

