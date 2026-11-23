module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import GroundTheory.PAdicHodge.BCrisRegularFinal
public import GroundTheory.PAdicHodge.FundamentalSeqBCris
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.NonemptyThetaLOfTied
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FilQuot
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.Bundle0002

@[expose] public section

noncomputable section

namespace PositivityTheory.LocInh

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per6

section Abstract

theorem onto_eigen {A C : Type} [CommRing A] [CommRing C] {k : A →+* C}
    (hk : Function.Injective k) {G : C →+* C} {g : A →+* A} (hG : ∀ x, G (k x) = k (g x))
    {p m n : ℕ} {a : A} {y : C} (ha : k a = k (p : A) ^ m * y) (hy : G y = (p : C) ^ n * y) :
    g a = (p : A) ^ n * a := by
  apply hk
  rw [← hG, map_mul, map_pow, ha, map_mul, map_pow, map_natCast, map_natCast, hy]
  ring

theorem onto_fixed {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} {F : B →+* B}
    {g : A →+* A} (hF : ∀ x, F (f x) = f (g x)) {p t a : A} (hf : IsFrac f p t) (hp : g p = p)
    (ht : g t = p * t) (m : ℕ) {n : ℕ} (ha : g a = p ^ n * a) :
    ∃ x : B, F x = x ∧ f p ^ m * f t ^ n * x = f a := by
  obtain ⟨x, hx⟩ := ((hf.1.pow m).mul (hf.2.1.pow n)).exists_right_inv
  have e : f p ^ m * f t ^ n * (x * f a) = f a := by rw [← mul_assoc, hx, one_mul]
  refine ⟨x * f a, ?_, e⟩
  have h1 := congrArg F e
  rw [map_mul, map_mul, map_pow, map_pow, hF, hF, hF, hp, ht, ha, map_mul f, map_mul f,
    map_pow f] at h1
  refine ((hf.1.pow m).mul ((hf.1.mul hf.2.1).pow n)).mul_left_cancel (h1.trans ?_)
  conv_lhs => rw [← e]
  ring

theorem onto_cancel {A C E : Type} [CommRing A] [CommRing C] [Field E] {k : A →+* C}
    {I : C →+* E} {c : A →+* E} (hI : ∀ x, I (k x) = c x) {p a : A} (hp : c p ≠ 0) {m : ℕ}
    {y : C} (ha : k a = k p ^ m * y) {z : E} (h : c a = c p ^ m * z) : z = I y := by
  have h1 := congrArg I ha
  rw [map_mul, map_pow, hI, hI, h] at h1
  exact mul_left_cancel₀ (pow_ne_zero m hp) h1

theorem onto_injective {A C E : Type} [CommRing A] [CommRing C] [Field E] {k : A →+* C}
    {I : C →+* E} {c : A →+* E} (hI : ∀ x, I (k x) = c x) (hc : Function.Injective c) :
    Function.Injective k := fun x y e => hc (by rw [← hI, ← hI, e])

theorem away_exists_self {A : Type} [CommRing A] {a : A} (y : Localization.Away a) :
    ∃ (k : ℕ) (x : A), algebraMap A (Localization.Away a) x =
      algebraMap A (Localization.Away a) a ^ k * y :=
  away_exists (RingHom.id _) _ (fun _ => rfl) y

end Abstract

section Concrete

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem onto_plus {y : ACris.BCrisPlus ℂ_[l] l} {n : ℕ}
    (hy : ACris.phiPlus ℂ_[l] l y = (l : ACris.BCrisPlus ℂ_[l] l) ^ n * y) :
    ∃ x : Per6.Bcris l, Per6.φB l x = x ∧ cD l (Per6.tA l) ^ n * ιCD l x = invPlusD l y := by
  obtain ⟨m, a, ha⟩ := away_exists_self y
  have h1 := onto_eigen (onto_injective invPlusD_algebraMap (cD_injective l))
    ACris.phiPlus_algebraMap ha hy
  obtain ⟨x, hx, e⟩ := onto_fixed φB_cB (cB_isFrac l) (map_natCast _ l) frob_phi_tA m h1
  exact ⟨x, hx, onto_cancel invPlusD_algebraMap (cD_l_ne_zero l) ha (inv_map_frac (ιCD_fac l) e)⟩

theorem cD_tA_eq : cD l (Per6.tA l) =
    algebraMap (Per6.BdRp l) (Per6.BdR l) (fontaineT (epsilon l) untilt_epsilon) :=
  congrArg (algebraMap (Per6.BdRp l) (Per6.BdR l)) (ACris.iota_periodT (untilt_epsilon (p := l)))

theorem fund_onto (z : Per6.BdR l) : ∃ x : Per6.Bcris l, Per6.φB l x = x ∧
    ∃ c : Per6.BdRp l, ιCD l x - z = algebraMap (Per6.BdRp l) (Per6.BdR l) c := by
  obtain ⟨n, w, hs⟩ := ACris.exists_mul_pow_fontaineT_eq (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one z
  obtain ⟨y, hy, hyw⟩ := ACris.exists_phiPlus_eq_pow_iotaPlus_sub_mem (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one (m := n) (n := n) le_rfl w
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyw
  obtain ⟨x, hx, e⟩ := onto_plus hy
  rw [cD_tA_eq] at e
  exact ⟨x, hx, c, ACris.sub_eq_map_of_pow_mul (algebraMap (Per6.BdRp l) (Per6.BdR l))
    (cD_tA_eq (l := l) ▸ cD_tA_ne_zero l) e hs hc⟩

section Eps

variable {ε : PreTilt (normInteger ℂ_[l]) l} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l).symm ε) ≠ 1)




end Eps


end Concrete

end PositivityTheory.LocInh
