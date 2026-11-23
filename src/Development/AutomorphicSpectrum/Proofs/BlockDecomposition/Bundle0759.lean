module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0756
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0754
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0552
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepClassDecomposition
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MPDict.ClsRep

open GlobalTheory.CompanionTheory.MPDict.IsomT GlobalTheory.CompanionTheory.MPDict.TensRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def HasFrame (L : LB (MP ℤ m n)) (a : Fin (m + 1) → ℤ) : Prop :=
  ∃ u : ∀ (i : L.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, L.U i ⊓ mchart c)ˣ,
    (∀ i j c,
      Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          L.U i ⊓ L.U j ⊓ mchart c ≤ L.U j ⊓ mchart c) (u j c) =
        Semi.res (inf_le_left : L.U i ⊓ L.U j ⊓ mchart c ≤ L.U i ⊓ L.U j) (L.g i j) *
          Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            L.U i ⊓ L.U j ⊓ mchart c ≤ L.U i ⊓ mchart c) (u i c)) ∧
    (∀ i c c',
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          L.U i ⊓ (mchart c ⊓ mchart c') ≤ L.U i ⊓ mchart c) (u i c) =
        Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          L.U i ⊓ (mchart c ⊓ mchart c') ≤ L.U i ⊓ mchart c') (u i c') *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            L.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ a k)

theorem hasFrame_of_isHermRep {M : HermLB (mpStr ℤ m n)} {A : Geo.HermLine (Bk n)} (h : IsHermRep M A) :
    HasFrame M.B A.a := by
  obtain ⟨u, h₁, h₂, -⟩ := h
  exact ⟨u, h₁, h₂⟩

theorem iSup_mchart : ⨆ c : (∀ k, Bk n k), mchart c = (⊤ : (MP ℤ m n).Opens) := by
  refine top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨fun k => ptChart x k, ?_⟩
  exact Set.mem_iInter.2 fun k => mem_ptChart x k

theorem cg₃ {G : Type*} [CommGroup G] {x x' y y' P : G} (h : x = x' * P) (h' : y = y' * P) :
    x * y⁻¹ = x' * y'⁻¹ := by
  subst h h'
  rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]

theorem cg₄ {G : Type*} [CommGroup G] {x x' y y' g g' : G} (h : x' = g' * x) (h' : y' = g * y) :
    x * y⁻¹ = g * g'⁻¹ * (x' * y'⁻¹) := by
  subst h h'
  simp only [mul_inv]
  rw [show g * g'⁻¹ * (g' * x * (g⁻¹ * y⁻¹)) = (g * g⁻¹) * (g'⁻¹ * g') * (x * y⁻¹) by ac_rfl]
  simp

theorem lbIso_of_hasFrame {L N : LB (MP ℤ m n)} {a : Fin (m + 1) → ℤ} (hL : HasFrame L a) (hN : HasFrame N a) :
    LBIso L N := by
  obtain ⟨u, u₁, u₂⟩ := hL
  obtain ⟨v, v₁, v₂⟩ := hN
  have hglue (p : N.ι × L.ι) : ∃ t : Γ(MP ℤ m n, N.U p.1 ⊓ L.U p.2)ˣ, ∀ c,
      Semi.res inf_le_left t =
        Semi.res (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ L.U p.2 ⊓ mchart c) (u p.2 c) *
        (Semi.res (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ N.U p.1 ⊓ mchart c) (v p.1 c))⁻¹ := by
    refine exists_glue mchart iSup_mchart _ _ fun c c' => ?_
    have e₁ := (congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.2, hx.1.2, hx.2.2⟩ :
      ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ L.U p.2 ⊓ (mchart c ⊓ mchart c'))) (u₂ p.2 c c')).trans
      (res_mul_prod c c' a _ _ _)
    have e₂ := (congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.1, hx.1.2, hx.2.2⟩ :
      ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ N.U p.1 ⊓ (mchart c ⊓ mchart c'))) (v₂ p.1 c c')).trans
      (res_mul_prod c c' a _ _ _)
    simp only [map_mul, map_inv, res_twice] at e₁ e₂ ⊢
    exact cg₃ e₁ e₂
  choose t ht using hglue
  have htT (p : N.ι × L.ι) (c : ∀ k, Bk n k) {T : (MP ℤ m n).Opens} (hT : T ≤ (N.U p.1 ⊓ L.U p.2) ⊓ mchart c) :
      Semi.res (hT.trans inf_le_left) (t p) =
        Semi.res (ofMem fun _ hx => ⟨(hT hx).1.2, (hT hx).2⟩ : T ≤ L.U p.2 ⊓ mchart c) (u p.2 c) *
        (Semi.res (ofMem fun _ hx => ⟨(hT hx).1.1, (hT hx).2⟩ : T ≤ N.U p.1 ⊓ mchart c) (v p.1 c))⁻¹ := by
    have e := congrArg (Semi.res hT) (ht p c)
    simpa only [map_mul, map_inv, res_twice] using e
  refine ⟨⟨t⟩, fun (p q : N.ι × L.ι) => units_ext_cover mchart iSup_mchart fun c => ?_⟩
  change Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2))
      (Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ L.U p.2) (t p)) =
    Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2))
      ((Semi.res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1) *
        (Semi.res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹) *
        Semi.res (inf_le_right : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U q.1 ⊓ L.U q.2) (t q))
  simp only [map_mul, map_inv, res_twice]
  rw [htT p c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩),
    htT q c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩)]
  have hU : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ L.U p.2 ⊓ L.U q.2 ⊓ mchart c :=
    ofMem fun _ hx => ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2⟩
  have hV : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ N.U p.1 ⊓ N.U q.1 ⊓ mchart c :=
    ofMem fun _ hx => ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2⟩
  have e₁ := congrArg (Semi.res hU) (u₁ p.2 q.2 c)
  have e₂ := congrArg (Semi.res hV) (v₁ p.1 q.1 c)
  simp only [map_mul, res_twice] at e₁ e₂
  exact cg₄ e₁ e₂

theorem hasFrame_tens {L N : LB (MP ℤ m n)} {a b : Fin (m + 1) → ℤ} (hL : HasFrame L a) (hN : HasFrame N b) :
    HasFrame (GlobalTheory.CechPic.tens L N) (a + b) := by
  obtain ⟨u, hu₁, hu₂⟩ := hL
  obtain ⟨v, hv₁, hv₂⟩ := hN
  refine ⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ c
    exact frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _
  · rintro ⟨i, i'⟩ c c'
    exact mono_mulUnit a b _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _

theorem hasFrame_dual {L : LB (MP ℤ m n)} {a : Fin (m + 1) → ℤ} (hL : HasFrame L a) :
    HasFrame (GlobalTheory.CechPic.dual L) (-a) := by
  obtain ⟨u, h1, h2⟩ := hL
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_⟩
  · intro i j c
    have e := h1 i j c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (L.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv]
    exact (congrArg (·⁻¹) e).trans (mul_inv _ _)
  · intro i c c'
    have e := h2 i c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-a k)
    simp only [zpow_neg, Finset.prod_inv_distrib, map_inv]
    exact (congrArg (·⁻¹) e).trans (mul_inv _ _)

theorem hasFrame_triv : HasFrame (LB.triv (MP ℤ m n)) 0 := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
  · intro i c c'
    simp

theorem res_pullO_g (k : Fin (m + 1)) (i j : Bk n k) {V : (MP ℤ m n).Opens}
    (h : V ≤ (pullO (prB n k) 1).U i ⊓ (pullO (prB n k) 1).U j) :
    Semi.res h ((pullO (prB n k) 1).g i j) = blockUnit i j h := by
  refine Units.ext ((val_res_pullO_g (prB n k) 1 i j h).trans ?_)
  rw [pow_one]
  exact (GlobalTheory.CompanionTheory.MPDict.Inhab.val_blockUnit i j h).symm

theorem hasFrame_pullO (k : Fin (m + 1)) : HasFrame (pullO (prB n k) 1) (Pi.single k 1) := by
  refine ⟨fun i c => blockUnit (c k) i (le_inf (inf_le_right.trans (mchart_le c k)) inf_le_left), ?_, ?_⟩
  · intro i j c
    refine (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (res_pullO_g k i j _) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)).symm)
    rw [mul_comm]
    exact (GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm
  · intro i c c'
    refine (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)
        (GlobalTheory.CompanionTheory.MPDict.Inhab.prod_blockUnit_single k c c' _)).symm)
    rw [mul_comm]
    exact (GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm

theorem exists_hasFrame_cls (a : Fin (m + 1) → ℤ) : ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧
    cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  classical
  let H : AddSubgroup (Fin (m + 1) → ℤ) :=
    { carrier := {a | ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧
        cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1)}
      add_mem' := by
        rintro a b ⟨L, hL, fL, eL⟩ ⟨N, hN, fN, eN⟩
        refine ⟨_, isLB_tens hL hN, hasFrame_tens fL fN, ?_⟩
        rw [cls_tens hL hN, eL, eN, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => (add_smul _ _ _).symm
      zero_mem' := ⟨_, LB.isLB_triv _, hasFrame_triv, by simp; rfl⟩
      neg_mem' := by
        rintro a ⟨L, hL, fL, eL⟩
        refine ⟨_, isLB_dual hL, hasFrame_dual fL, ?_⟩
        rw [cls_dual hL, eL, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => (neg_smul _ _).symm }
  have hs (k : Fin (m + 1)) : (Pi.single k 1 : Fin (m + 1) → ℤ) ∈ H := by
    refine ⟨_, isLB_pullO _ 1, hasFrame_pullO k, ?_⟩
    rw [Finset.sum_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
      Pi.single_eq_same, one_smul]
  have e : a = ∑ k, a k • (Pi.single k 1 : Fin (m + 1) → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have : a ∈ H := e ▸ H.sum_mem fun k _ => H.zsmul_mem (hs k) _
  exact this

end GlobalTheory.CompanionTheory.MPDict.ClsRep

theorem GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → cls M.B M.isLB = ∑ k, A.a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  intro m n M A h
  obtain ⟨L, hL, fL, eL⟩ := GlobalTheory.CompanionTheory.MPDict.ClsRep.exists_hasFrame_cls (m := m) (n := n) A.a
  exact ((cls_eq_iff M.isLB hL).2 (GlobalTheory.CompanionTheory.MPDict.ClsRep.lbIso_of_hasFrame
    (GlobalTheory.CompanionTheory.MPDict.ClsRep.hasFrame_of_isHermRep h) fL)).trans eL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLMWordSOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcB.F.MLM (wordLS wordUS CtStar)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchWordS

open GlobalTheory.CompanionTheory.MatchWord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isHecke_lstar {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) : IsHecke (KL n w) (lstar f) := by
  refine ⟨(hf.1.comp_homeomorph (Homeomorph.inv _)).comp_left (map_zero (starRingEnd ℂ)), fun k hk x => ⟨?_, ?_⟩⟩
  · simp only [lstar, _root_.mul_inv_rev, (hf.2 _ (inv_mem hk) _).2]
  · simp only [lstar, _root_.mul_inv_rev, (hf.2 _ (inv_mem hk) _).1]

def letU (d : LocData E n) (w : Pl E) (x : ℕ × Bool × Bool) : UL n w → ℂ :=
  if x.2.2 then lstar (d.hU w x.1) else d.hU w x.1

def letL (d : LocData E n) (a : ℕ) (ha : a ≤ n) (w : Pl E) (x : ℕ × Bool × Bool) : LM d.kap a (n - a) :=
  if x.2.2 then (d.hL a ha w x.1 x.2.1).adj else d.hL a ha w x.1 x.2.1

theorem word_ct (d : LocData E n) (a : ℕ) (ha : a ≤ n) {w : Pl E} (hCt : MT.CtMul) (hSt : CtStar) (hSp : SphComm) (hE : Unr E)
    (hd : d.Ok) (hG : d.Good w) (hN : ∀ u, ‖((d.μ w u : ℂˣ) : ℂ)‖ = 1) (l : List (ℕ × Bool × Bool)) :
    IsHecke (KL n w) (wordUS d w l) ∧ ∃ A B : UL n w → ℂ, IsHecke (KL n w) A ∧ IsHecke (KL n w) B ∧
      (wordLS d a ha w l).s w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A ∧
      (wordLS d a ha w l).t w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B ∧
      mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A) (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B) =
        ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l) := by
  have hG' := hG
  obtain ⟨hw, hT, hS₀, hBad, hμ⟩ := hG
  have hU : UL n w = ⊤ := if_pos hw
  set C := ctMu (Nat.add_sub_cancel' ha) w (d.μ w) with hC
  have conv : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → IsHecke (KL n w) (lconv f g) :=
    fun hf hg => GlobalTheory.CompanionTheory.UnitaryWord.isHecke_lconv GlobalTheory.CompanionTheory.LocHecke.locAlg (GlobalTheory.CompanionTheory.MatchPowers.isLevel_KL n w) hf hg
  have mul : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → C (lconv f g) = mconv (C f) (C g) :=
    fun hf hg => hCt E n a ha w hw (d.μ w) hμ _ _ hf hg
  have star : ∀ {f : UL n w → ℂ}, IsHecke (KL n w) f → lfStar (C f) = C (lstar f) :=
    fun hf => (hSt E n a ha w hw (d.μ w) hN _ hf).symm
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have hunit : C (lone (KL n w)) = PositivityTheory.Rg.BcB.F.idem (K2 a (n - a) w) := GlobalTheory.CompanionTheory.MatchUnit.ctMu_lone _ hU _ hμ
  have hlev : d.lev a w = K2 a (n - a) w := by
    unfold LocData.lev
    rw [if_neg hT, if_neg (by simp [hS₀, hBad])]
  have hlev₂ : d.lev₂ a w = K2 a (n - a) w := by
    unfold LocData.lev₂
    rw [if_neg (by simp [hS₀, hBad])]
  have hes : (d.eL a).s w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev a w) = _
    rw [hlev]
  have het : (d.eL a).t w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev₂ a w) = _
    rw [hlev₂]
  have hstar1 : lfStar (C (lone (KL n w))) = C (lone (KL n w)) := by
    rw [hunit, PositivityTheory.Rg.BcB.F.LocComm.lfStar_idem]
  have hH : ∀ x, IsHecke (KL n w) (letU d w x) := by
    rintro ⟨k, intersection_update_fsHerm_neg_one, st⟩
    have hTk := isHecke_hU d hd hU k
    cases st
    · exact hTk
    · exact isHecke_lstar hTk
  have hck : ∀ k, d.hc a ha w k = C (d.hU w k) := fun k => hc_eq d a ha hμ k
  have hl0 : ∀ k st, (letL d a ha w (k, false, st)).s w = C (letU d w (k, false, st)) ∧
      (letL d a ha w (k, false, st)).t w = C (lone (KL n w)) := by
    intro k st
    have e : (d.hL a ha w k false).s w = d.hc a ha w k := by simp [LocData.hL]
    cases st
    · exact ⟨by simpa [letL, letU] using e.trans (hck k), het⟩
    · refine ⟨?_, ?_⟩
      · show lfStar ((d.hL a ha w k false).s w) = C (lstar (d.hU w k))
        rw [e, hck, star (isHecke_hU d hd hU k)]
      · show lfStar ((d.eL a).t w) = _
        rw [het, hstar1]
  have hl1 : ∀ k st, (letL d a ha w (k, true, st)).s w = C (lone (KL n w)) ∧
      (letL d a ha w (k, true, st)).t w = C (letU d w (k, true, st)) := by
    intro k st
    have e : (d.hL a ha w k true).t w = d.hc a ha w k := by simp [LocData.hL]
    cases st
    · exact ⟨hes, by simpa [letL, letU] using e.trans (hck k)⟩
    · refine ⟨?_, ?_⟩
      · show lfStar ((d.eL a).s w) = _
        rw [hes, hstar1]
      · show lfStar ((d.hL a ha w k true).t w) = C (lstar (d.hU w k))
        rw [e, hck, star (isHecke_hU d hd hU k)]
  induction l with
  | nil =>
    refine ⟨?_, lone (KL n w), lone (KL n w), hone, hone, hes, het, ?_⟩
    · show IsHecke (KL n w) ((KL n w : Set (UL n w)).indicator 1)
      rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL] at hone
      exact hone
    · rw [← mul hone hone, lconv_lone_left hone, GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
      rfl
  | cons x l ih =>
    obtain ⟨hW, A, B, hA, hB, hs, ht, hm⟩ := ih
    obtain ⟨k, intersection_update_fsHerm_neg_one, st⟩ := x
    have hg := hH (k, intersection_update_fsHerm_neg_one, st)
    have hWc : wordUS d w ((k, intersection_update_fsHerm_neg_one, st) :: l) = lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) (wordUS d w l) := rfl
    have hLc : wordLS d a ha w ((k, intersection_update_fsHerm_neg_one, st) :: l) = (letL d a ha w (k, intersection_update_fsHerm_neg_one, st)).mul (wordLS d a ha w l) := rfl
    have key : mconv (C (lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) A)) (C B) = C (lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) (wordUS d w l)) := by
      rw [← mul (conv hg hA) hB, lconv_assoc hE hg hA hB, mul hg (conv hA hB), mul hA hB, hm, ← mul hg hW]
    refine ⟨hWc ▸ conv hg hW, ?_⟩
    rw [hWc, hLc]
    cases intersection_update_fsHerm_neg_one with
    | false =>
      obtain ⟨e₁, e₂⟩ := hl0 k st
      refine ⟨lconv (letU d w (k, false, st)) A, B, conv hg hA, hB, ?_, ?_, key⟩
      · show mconv ((letL d a ha w (k, false, st)).s w) ((wordLS d a ha w l).s w) = _
        rw [e₁, hs, ← mul hg hA]
      · show mconv ((letL d a ha w (k, false, st)).t w) ((wordLS d a ha w l).t w) = _
        rw [e₂, ht, ← mul hone hB, lconv_lone_left hB]
    | true =>
      obtain ⟨e₁, e₂⟩ := hl1 k st
      refine ⟨A, lconv (letU d w (k, true, st)) B, hA, conv hg hB, ?_, ?_, ?_⟩
      · show mconv ((letL d a ha w (k, true, st)).s w) ((wordLS d a ha w l).s w) = _
        rw [e₁, hs, ← mul hone hA, lconv_lone_left hA]
      · show mconv ((letL d a ha w (k, true, st)).t w) ((wordLS d a ha w l).t w) = _
        rw [e₂, ht, ← mul hg hB]
      · rw [← mul hA (conv hg hB), ← lconv_assoc hE hA hg hB, mul (conv hA hg) hB, mul hA hg,
          hSp E a (n - a) w (C A) (C (letU d w (k, true, st))) (isHecke_ctMu _ hU _ hμ hA) (isHecke_ctMu _ hU _ hμ hg),
          ← mul hg hA]
        exact key

theorem matchLMWordSOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := by
  intro hS hCt hSt hSp _ E _ _ _ hE n d hd a ha w hG hN l
  have hP : w ∉ d.P := by simp [LocData.P, hG.2.1, hG.2.2.1]
  have htr : (wordLS d a ha w l).tr d.P d.one w = (wordLS d a ha w l).s w := if_neg hP
  obtain ⟨hW, A, B, -, -, hs, ht, hm⟩ := word_ct d a ha hCt hSt hSp hE hd hG hN l
  rw [htr, hs, ht, hm]
  have hμ := hG.2.2.2.2
  have hw := hG.1
  have h1 := hS E n a ha w hw (d.μ w) hμ _ hW 1 le_rfl
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have e1 : lpow (KL n w) (wordUS d w l) 1 = wordUS d w l := lconv_lone_right hW
  have e2 : mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l))
      (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w))) =
      ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l) := by
    rw [← hCt E n a ha w hw (d.μ w) hμ _ _ hW hone, lconv_lone_right hW]
  rw [e1] at h1
  exact e2 ▸ h1

end GlobalTheory.CompanionTheory.MatchWordS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparablePowerTorus
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MLM Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SepPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem zpow_mul_inj {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {a c : ℤ} {u v : w.adicCompletion E}
    (hu : Valued.v u = 1) (hv : Valued.v v = 1)
    (h : ((ϖ ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * u = ((ϖ ^ c : (w.adicCompletion E)ˣ) : w.adicCompletion E) * v) :
    a = c := by
  have e := congrArg Valued.v h
  rw [map_mul, map_mul, hu, hv, mul_one, mul_one] at e
  have h1 : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [GlobalTheory.BorelUMod.v_eq_exp ϖ.ne_zero, hϖ.1]
  have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by
    rw [h1]; exact WithZero.exp_ne_zero
  have hne : Valued.v (ϖ : w.adicCompletion E) ≠ 1 := by
    rw [h1, ← WithZero.exp_zero]
    intro h2
    have := WithZero.exp_injective h2
    omega
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀] at e
  exact zpow_right_injective₀ (zero_lt_iff.2 h0) hne e

theorem separable_of_fU {w : Pl E} {b : GLw n w} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {l : Fin (n / 2) → ℤ}
    (hl : Cone l) {γ : UL n w} (h : fU n w b ϖ l γ ≠ 0) : γ.1.val.charpoly.Separable := by
  have hy := (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1
  have h' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
    by_contra hc
    exact h (if_neg hc)
  obtain ⟨x, hx, z, hz, e⟩ := h'
  obtain ⟨x', hx', ex⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
  obtain ⟨z', hz', ez⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hz)
  have ex' : x.1 = b * x' * b⁻¹ := ex.symm
  have ez' : z.1 = b * z' * b⁻¹ := ez.symm
  have hδ : dcos n w (tdiag ϖ (wexp n l)) (b⁻¹ * γ.1 * b) ≠ 0 := by
    have : ∃ p ∈ iwGL n w, ∃ q ∈ iwGL n w, b⁻¹ * γ.1 * b = p * tdiag ϖ (wexp n l) * q :=
      ⟨x', hx', z', hz', by rw [e, ex', ez']; group⟩
    simp [dcos, this]
  obtain ⟨m, -, τ, hτ, em⟩ := GlobalTheory.CompanionTheory.IwahoriContraction.contr_id w ϖ hϖ n (wexp n l) hy _ hδ
  have hval : (tdiag ϖ (wexp n l) * τ).val = Matrix.diagonal fun i =>
      ((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * τ.val i i := by
    have hτd : τ.val = Matrix.diagonal fun i => τ.val i i := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · rw [hτ.1 i j hij, Matrix.diagonal_apply_ne _ hij]
    rw [Units.val_mul, GlobalTheory.CompanionTheory.FUMulPf.tdiag_val, hτd, Matrix.diagonal_mul_diagonal]
    simp
  have hg : γ.1 = (b * m) * (tdiag ϖ (wexp n l) * τ) * (b * m)⁻¹ := by
    rw [← em]; group
  rw [GlobalTheory.CompanionTheory.UnitarySide.charpoly_conj_diagonal (b * m) _ γ.1 _ hval hg, Polynomial.separable_prod_X_sub_C_iff]
  intro i j hij
  exact hy.injective (zpow_mul_inj hϖ (hτ.2 i) (hτ.2 j) hij)

theorem sepPowT : SepPowT := by
  intro E _ _ _ hU n d hd hm m w hT y hy
  obtain ⟨hs, hb, hϖ, hx⟩ := hm.T w hT
  have hx' : ∀ j, StrictAnti (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j) ∧ Cone (lOf (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j)) :=
    fun j => hx j.1 j.2
  obtain ⟨J', _, c', x', hx'', e1, -⟩ := GlobalTheory.CompanionTheory.MatchPow.pow_claim GlobalTheory.CompanionTheory.FUMulPf.fuMul GlobalTheory.CompanionTheory.DcosProduct.dcosMul hU hs 0
    hb hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w) hx' m
  have hKU : d.KU w = iwU n w (d.b w) := by simp [LocData.KU, hT]
  have hG : d.gU (m + 1) w y = (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1) *
      (GlobalTheory.CompanionTheory.MatchPow.alpha n w (d.b w) ^ m * ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y) := by
    unfold LocData.gU
    rw [hKU, GlobalTheory.CompanionTheory.MatchLMPlaces.unitary_function_at_T d hT, GlobalTheory.CompanionTheory.MatchLMPlaces.lpow_scale, e1]
  rw [hG] at hy
  have hsum : ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y ≠ 0 := fun h0 => hy (by rw [h0]; simp)
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact separable_of_fU hϖ (hx'' j).2 (right_ne_zero_of_mul hj)

end GlobalTheory.CompanionTheory.SepPow

end
end

