module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0645
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingIdentityOf

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcB.F.MLM (muAt MOk MatchLMB2)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchLMB2

section Scale

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Scale

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mconv_left {a b : ℕ} {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} {f : LF a b w} (g : LF a b w)
    (hf : ∀ u ∈ U, ∀ x, f (u * x) = f x) {u : GLw a w × GLw b w} (hu : u ∈ U) (m : GLw a w × GLw b w) :
    mconv f g (u * m) = mconv f g m := by
  unfold mconv
  rw [← GlobalTheory.CompanionTheory.CtMulSplit.hint_left _ u]
  congr 1
  funext z
  rw [hf u hu z]
  congr 2
  group

theorem tr_one (d : LocData E n) {a : ℕ} (L : LM d.kap a (n - a)) {w : Pl E} (hw : w ∈ d.P) :
    L.tr d.P d.one w = ∑ x, L.m w x x := by
  unfold LM.tr
  rw [if_pos hw]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · simp [LocData.one]
  · intro y _ hy
    simp [LocData.one, hy]
  · simp

theorem sum_kap_alt (d : LocData E n) {w : Pl E} (hT : w ∈ d.T) {M : Type} [AddCommMonoid M]
    (F : Finset (Fin (n / 2)) → M) : ∑ x : d.kap w, F x.1.1 = ∑ s, F s := by
  have e : d.idx w = Finset.univ ×ˢ {1} := by
    unfold LocData.idx
    rw [if_pos hT]
  rw [Finset.sum_coe_sort (d.idx w) (fun p => F p.1), e, Finset.sum_product]
  simp

end Alg

section TPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem qT_mpow_left (d : LocData E n) {a : ℕ} (w : Pl E) (s : Finset (Fin (n / 2))) (k : ℕ)
    {u : GLw a w × GLw (n - a) w} (hu : u ∈ I2 a (n - a) w) (g : GLw a w × GLw (n - a) w) :
    MT.mpow w (d.qT a w s) (k + 1) (u * g) = MT.mpow w (d.qT a w s) (k + 1) g :=
  mconv_left _ (fun _ hv t => (GlobalTheory.CompanionTheory.MatchId.qT_inv d s hv t).1) hu g

theorem powers_diagonal_at_T_block (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hT : w ∈ d.T) (k : ℕ) (x y : d.kap w) :
    (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) k).m w x y = d.diag (fun x => MT.mpow w (d.qT a w x.1.1) (k + 1)) x y := by
  have hb : ∀ x y : d.kap w, (d.betaL a ha).m w x y = d.diag (fun x => d.qT a w x.1.1) x y := fun x y => by
    show (if w ∈ d.T then _ else _) = _
    rw [if_pos hT]
  induction k generalizing x y with
  | zero =>
    show (d.betaL a ha).m w x y = _
    rw [hb]
    unfold LocData.diag
    split_ifs
    · exact (GlobalTheory.CompanionTheory.FmPowP.mconv_idem_right (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open a (n - a) w) (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_le_maximal a (n - a) w)
        (d.qT a w x.1.1) fun u hu g => (GlobalTheory.CompanionTheory.MatchId.qT_inv d _ hu g).2).symm
    · rfl
  | succ k ih =>
    show ∑ z, mconv ((d.betaL a ha).m w x z) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) k).m w z y) = _
    simp only [hb, ih]
    rw [GlobalTheory.CompanionTheory.MatchId.sum_mconv_diag_left d (fun z => d.diag (fun x => MT.mpow w (d.qT a w x.1.1) (k + 1)) z y)]
    unfold LocData.diag
    split_ifs with h
    · rfl
    · exact GlobalTheory.CompanionTheory.MatchId.mconv_zero_right _

theorem trace_test_function_eq (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hT : w ∈ d.T) (m : ℕ) :
    ((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).tr d.P d.one w =
      fun y => ∑ s, MT.mpow w (d.qT a w s) (m + 1) y := by
  have hP : w ∈ d.P := Finset.mem_union_left _ hT
  have hlev : d.lev a w = I2 a (n - a) w := by
    unfold LocData.lev
    rw [if_pos hT]
  have hent : ∀ x : d.kap w, ((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).m w x x =
      MT.mpow w (d.qT a w x.1.1) (m + 1) := by
    intro x
    show ∑ z, mconv ((d.fixL a).m w x z) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w z x) = _
    have e : ∀ z, (d.fixL a).m w x z = d.diag (fun _ => PositivityTheory.Rg.BcB.F.idem (I2 a (n - a) w)) x z := fun z => by
      show d.diag (fun _ => if w ∈ d.T then PositivityTheory.Rg.BcB.F.idem (d.lev a w) else d.sgn a w • PositivityTheory.Rg.BcB.F.idem (d.lev a w)) x z = _
      rw [if_pos hT, hlev]
    simp only [e]
    rw [GlobalTheory.CompanionTheory.MatchId.sum_mconv_diag_left d (fun z => (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w z x), powers_diagonal_at_T_block d ha hT]
    unfold LocData.diag
    rw [if_pos rfl]
    exact GlobalTheory.CompanionTheory.FmPowP.mconv_idem_left (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open a (n - a) w) (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_le_maximal a (n - a) w) _
      fun u hu g => qT_mpow_left d w _ m hu g
  rw [tr_one d _ hP]
  funext y
  rw [Finset.sum_apply]
  simp only [hent]
  exact sum_kap_alt d hT (fun s => MT.mpow w (d.qT a w s) (m + 1) y)

end TPlace

section SPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end SPlace

section BadPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end BadPlace

end GlobalTheory.CompanionTheory.MatchLMB2

end
