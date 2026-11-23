module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittRankZeroEmbeddingMemLatticeCongruenceIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0626

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConnectionLinear
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {M : Vol G} {t : T}

theorem conAt_zero (hM : M.Is t) (Φ : SchDown G t) (h : Pts G) (j : ℕ) (hj : Even j) (hm : ¬ (Even D.R.m ∧ j + 2 ≤ D.R.m)) :
    conAt W hM Φ h j = 0 := by
  unfold conAt
  split_ifs with h1 h2
  · exfalso; apply hm; refine ⟨?_, by omega⟩; rw [← h1]; simpa [Nat.even_add] using hj
  · exfalso; apply hm; refine ⟨?_, by omega⟩; rw [← h2]; obtain ⟨r, hr⟩ := hj; exact ⟨r + ((D.R.m - 4 - j) / 2 + 1) + 1, by omega⟩
  · exact dif_neg h2

theorem conAt_local (hM : M.Is t) (Φ Φ' : SchDown G t) (h : Pts G) (j : ℕ)
    (hΦ : ∀ a : Fin D.R.m, ((a : ℕ) = j ∨ (a : ℕ) = j + 1) → Φ a = Φ' a) : conAt W hM Φ h j = conAt W hM Φ' h j := by
  have key : ∀ (a : ℕ) (ha : a < D.R.m), (a = j ∨ a = j + 1) → Φ ⟨a, ha⟩ = Φ' ⟨a, ha⟩ := fun a ha e => hΦ ⟨a, ha⟩ e
  unfold conAt
  simp (disch := simp) only [key]

theorem sum_eq_zero_of_multilin {ι I : Type} [Fintype ι] [dI : DecidableEq ι] {Y : ι → Type} (V : ∀ j, Submodule ℂ (Y j → ℂ))
    (E : (∀ j, Y j → ℂ) → ℂ)
    (hE : ∀ Φ : ∀ j, Y j → ℂ, (∀ j, Φ j ∈ V j) → ∀ a (φ φ' : Y a → ℂ) (c : ℂ), φ ∈ V a → φ' ∈ V a →
      E (Function.update Φ a (c • φ + φ')) = c * E (Function.update Φ a φ) + E (Function.update Φ a φ'))
    (S : Finset I) (x : I → ℂ) (Φ : I → ∀ j, Y j → ℂ) (hΦ : ∀ i ∈ S, ∀ j, Φ i j ∈ V j)
    (h0 : ∀ v : ∀ j, Y j, ∑ i ∈ S, x i * ∏ j, Φ i j (v j) = 0) : ∑ i ∈ S, x i * E (Φ i) = 0 := by
  have coe_upd : ∀ (m : ∀ j, V j) (a : ι) (p : V a),
      (fun j => ((Function.update m a p j : V j) : Y j → ℂ)) = Function.update (fun j => (m j : Y j → ℂ)) a (p : Y a → ℂ) :=
    fun m a p => funext fun j => Function.apply_update (fun j (z : V j) => (z : Y j → ℂ)) m a p j
  let Mm : MultilinearMap (RingHom.id ℂ) (fun j => V j) ℂ :=
    { toFun := fun m => E fun j => (m j : Y j → ℂ)
      map_update_add' := by
        intro inst m a p q
        obtain rfl : inst = dI := Subsingleton.elim _ _
        simp only [coe_upd, Submodule.coe_add]
        have := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a p q 1 p.2 q.2
        rw [one_smul, one_mul] at this
        exact this
      map_update_smul' := by
        intro inst m a c p
        obtain rfl : inst = dI := Subsingleton.elim _ _
        simp only [coe_upd, Submodule.coe_smul, smul_eq_mul]
        have := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a p 0 c p.2 (V a).zero_mem
        rw [add_zero] at this
        rw [this]
        have h00 := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a 0 0 1 (V a).zero_mem (V a).zero_mem
        simp only [smul_zero, add_zero, one_mul] at h00
        have hz : E (Function.update (fun j => (m j : Y j → ℂ)) a 0) = 0 := by linear_combination -h00
        rw [hz, add_zero]; rfl }
  classical
  let φ : I → ∀ j, V j := fun i j => if hi : i ∈ S then ⟨Φ i j, hΦ i hi j⟩ else 0
  let τ : I →₀ ℂ := Finsupp.onFinset S (fun i => if i ∈ S then x i else 0) (fun i hi => by by_contra h; simp [h] at hi)
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq V Mm τ 0 φ φ (fun z => by
    rw [Finsupp.sum_zero_index, Finsupp.onFinset_sum _ (fun _ => zero_mul _)]
    rw [← h0 z]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [φ, hi])
  rw [Finsupp.sum_zero_index] at key
  dsimp only [τ] at key
  rw [Finsupp.onFinset_sum _ (g := fun a c => c • Mm (φ a)) (fun _ => zero_smul _ _)] at key
  rw [← key]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [φ, hi, Mm]
end GlobalTheory.ConnectionLinear

namespace GlobalTheory.ConnectionLinear

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def PositionLinAt (j off : ℕ) : Prop :=
  ∀ t (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (Φ : SchDown ch.G t) (a : Fin D.R.m), (a : ℕ) = j + off →
    ∀ (φ φ' : Sch ch.G (.down t D.R.m a)) (c : ℂ), (∀ b, IsThetaFunO ch.W.ψ _ _ (Φ b)) → IsThetaFunO ch.W.ψ _ _ φ →
      IsThetaFunO ch.W.ψ _ _ φ' → ∀ u v,
      conAt ch.W hM (fockD ch.W t (Function.update Φ a (c • φ + φ')) P) h j u v =
        c * conAt ch.W hM (fockD ch.W t (Function.update Φ a φ) P) h j u v +
          conAt ch.W hM (fockD ch.W t (Function.update Φ a φ') P) h j u v

def ContrLin (off : ℕ) : Prop := ∀ j, Even j → j + 2 < D.R.m → Even D.R.m → PositionLinAt ch j off

def LastLin (off : ℕ) : Prop := ∀ j, Even j → j + 2 = D.R.m → PositionLinAt ch j off

theorem conLin_of_positions (hC0 : ContrLin ch 0) (hC1 : ContrLin ch 1) (hL0 : LastLin ch 0) (hL1 : LastLin ch 1) :
    ConLin ch := by
  intro t M hM P h I S x f Φ hΦ h0 u y
  have intersection_update_fsHerm_neg_one : ∀ j off, Even j → off ≤ 1 → PositionLinAt ch j off := by
    intro j off hj ho
    by_cases hm : Even D.R.m ∧ j + 2 ≤ D.R.m
    · rcases Nat.lt_or_eq_of_le hm.2 with hlt | heq
      · interval_cases off
        · exact hC0 j hj hlt hm.1
        · exact hC1 j hj hlt hm.1
      · interval_cases off
        · exact hL0 j hj heq
        · exact hL1 j hj heq
    · intro t M hM P h Φ a _ φ φ' c _ _ _ u v
      simp only [conAt_zero ch.W hM _ h j hj hm, Pi.zero_apply, mul_zero, add_zero]
  let E : SchDown ch.G t → ℂ := fun Ψ => ∏ k ∈ Finset.range (D.R.m / 2),
    conAt ch.W hM (fockD ch.W t Ψ P) h (2 * k) (u (2 * k)) (u (2 * k + 1))
  have hev : ∀ i, evT (conAt ch.W hM (fockD ch.W t (Φ i) P) h) (f i) u y = (∏ n, f i n (y n)) * E (Φ i) := fun i => by
    simp only [evT, E]; ring
  simp only [hev, ← mul_assoc]
  refine sum_eq_zero_of_multilin (fun j : Fin D.R.m => GlobalTheory.LastVertexInv.thSub ch.W (.mu t D.R.m (j : ℕ))) E ?_ S
    (fun i => x i * ∏ n, f i n (y n)) Φ (fun i hi j => hΦ i hi j) (fun v => ?_)
  · intro Ψ hΨ a φ φ' c hφ hφ'
    by_cases hm : Even D.R.m
    · have hk : (a : ℕ) / 2 ∈ Finset.range (D.R.m / 2) := by
        obtain ⟨r, hr⟩ := hm; have := a.2; rw [Finset.mem_range]; omega
      have hrest : ∀ ψ : Sch ch.G (.down t D.R.m a), ∏ k ∈ Finset.range (D.R.m / 2) \ {(a : ℕ) / 2},
          conAt ch.W hM (fockD ch.W t (Function.update Ψ a ψ) P) h (2 * k) (u (2 * k)) (u (2 * k + 1)) =
          ∏ k ∈ Finset.range (D.R.m / 2) \ {(a : ℕ) / 2},
          conAt ch.W hM (fockD ch.W t Ψ P) h (2 * k) (u (2 * k)) (u (2 * k + 1)) := by
        intro ψ
        refine Finset.prod_congr rfl fun k hk' => ?_
        have hk2 : k ≠ (a : ℕ) / 2 := by simpa using (Finset.mem_sdiff.1 hk').2
        rw [conAt_local ch.W hM (fockD ch.W t (Function.update Ψ a ψ) P) (fockD ch.W t Ψ P) h (2 * k) (fun b hb => ?_)]
        have hne : b ≠ a := fun e => by subst e; omega
        simp only [fockD, Function.update_of_ne hne]
      simp only [E]
      have hsplit := fun (g : ℕ → ℂ) => Finset.prod_eq_mul_prod_diff_singleton (s := Finset.range (D.R.m / 2)) ((a : ℕ) / 2) g (fun h' => absurd hk h')
      rw [hsplit, hsplit, hsplit, hrest, hrest, hrest]
      rw [intersection_update_fsHerm_neg_one (2 * ((a : ℕ) / 2)) ((a : ℕ) - 2 * ((a : ℕ) / 2)) (even_two_mul _) (by omega) t M hM P h Ψ a (by omega)
        φ φ' c hΨ hφ hφ']
      ring
    · have h0m : 0 ∈ Finset.range (D.R.m / 2) := by have := D.R.two_le_m; rw [Finset.mem_range]; omega
      have hz : ∀ Ψ' : SchDown ch.G t, E Ψ' = 0 := fun Ψ' => Finset.prod_eq_zero h0m (by
        rw [conAt_zero ch.W hM _ h (2 * 0) (even_two_mul 0) (fun e => hm e.1)]
        rfl)
      simp only [hz, mul_zero, add_zero]
  · rw [← h0 y v]
    exact Finset.sum_congr rfl fun i _ => by ring
end
end GlobalTheory.ConnectionLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal

noncomputable section

open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowShape

variable {D : D7}

def latPi (S : HSp D) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : GlobalTheory.FinPl.Lat S :=
  Submodule.pi Set.univ fun _ => (I : Submodule (𝓞 D.host.E) D.host.E)


variable (D) in
def tiltSc (j : ℕ) (p : Fin (D.R.m - 1 - j)) : D.host.E :=
  if Odd j then
    (if 2 * p.1 < D.R.m - 1 - j then (D.host.xi0 ^ p.1)⁻¹ else star (D.host.xi0 ^ (D.R.m - 1 - j - 1 - p.1)))
  else 1


variable (D) in
def rowId (j : ℕ) (p : Fin (D.R.m - 1 - j)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  FractionalIdeal.spanSingleton _ (tiltSc D j p) * stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) p

variable {T : Type} {L : LevCh D T} {sc : Consts}

def rowN (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (G.V (.grid D.R.m j)) :=
  if h : j < D.R.m then (G.rowDec j h).lat (G.Λ (.top j)) (rowId D j) else G.Λ (.grid D.R.m j)


variable (D) in
def lineId (j : ℕ) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  D.host.AA ^ ((D.R.m - 2 - j) / 2 + 1) * (D.host.AAbar ^ ((D.R.m - 2 - j) / 2 + 1))⁻¹


variable (D) in
def lineL (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.SeeSaw.Model.nLine D) := latPi _ (lineId D j)


variable (D) in
def topL : GlobalTheory.FinPl.Lat (GlobalTheory.RowChain.pLine D) := latPi _ 1

def coreL (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) :=
  (G.Λ (.top j)).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iA).restrictScalars
        (𝓞 D.host.E)) ⊔
    (lineL D j).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iB).restrictScalars
        (𝓞 D.host.E))

end GlobalTheory.RowShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthAtEmb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowChain.LastSeeSawStep

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem topOrthAt_emb (G : GridData L sc) {n : ℕ} (h : D.R.m = n) (h' : GA D (G.V (.grid D.R.m D.R.m))) :
    (topOrthAt G h).emb (h', 1) = topEmb G h h' := by
  subst h
  exact topOrth_emb G h'

theorem lastTau_gram :
    (lastTau (D := D))ᴴ * ((GlobalTheory.SeeSaw.Model.nLine D).gram * lastTau) =
      (-(D.host.xi0 * star D.host.xi0)) • (pLine D).gram := by
  refine Matrix.ext fun i j => ?_
  rw [pLine_gram]
  have h1 : ∀ a b : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank, (GlobalTheory.SeeSaw.Model.nLine D).gram a b = -1 := nLine_gram
  simp only [Matrix.mul_apply, conjTranspose_apply, lastTau, Matrix.of_apply, Matrix.smul_apply, h1]
  change ∑ x : Fin 1, star (-D.host.xi0) * ∑ y : Fin 1, (-1) * (-D.host.xi0) = (-(D.host.xi0 * star D.host.xi0)) * antiDiagonalSignGramMatrix (R := D.host.E) 1 1 i j
  have hij : i = j := Subsingleton.elim (α := Fin 1) _ _
  subst hij
  have hi : (i : ℕ) = 0 := by have := i.2; change (i : ℕ) < 1 at this; omega
  simp [antiDiagonalSignGramMatrix, hi]
  ring

end GlobalTheory.RowChain.LastSeeSawStep

namespace GlobalTheory.RowChain.LastSeeSawStep


set_option maxHeartbeats 2000000 in
theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : GlobalTheory.FunObj.Vol G}
    (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (F : Fn G (.grid D.R.m D.R.m))
    (φ : GA D (G.V (.top j)) → ℂ),
    IsThetaFunO Wl.ψ _ _ Φ₁ → IsThetaFunO Wl.ψ _ _ Φ₂ → IsContAut (G.V (.grid D.R.m D.R.m)) F → IsContAut (G.V (.top j)) φ →
    ∀ g : GA D (G.V (.grid D.R.m j)),
      (lastAt G Wl t hM j hj vN).Q φ ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) Φ₂ F =
        ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
          (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
          (lastDat Wl hM j hj vN g Φ₁ Φ₂) (topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m) := by
  intro D T L sc G Wl t M hM j hj vN Φ₁ Φ₂ F φ hΦ₁ hΦ₂ hF hφ g
  have hψ : IsStdChar D Wl.ψ (-1) := Wl.ψ_std
  obtain ⟨χz, hzH, hzE, -, hev, hodd⟩ := GlobalTheory.RowChars.rowChars G Wl t
  obtain ⟨hS0, hT0⟩ := hodd j (by omega) (by omega)
  obtain ⟨hS1, hT1⟩ := hev (j + 1) (by omega) (by omega)
  have homa : IsWeilDatumO Wl.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.chrS (.top t j)) (G.chrT (.top t j))
      (Wl.om (.top t j)) := Wl.om_is (.top t j) (by show j + 1 ≤ D.R.m; omega)
  have homX0 : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.chrS (.top t (j + 1)))
      (G.chrT (.top t (j + 1))) (Wl.om (.top t (j + 1))) := Wl.om_is (.top t (j + 1)) (by show j + 1 + 1 ≤ D.R.m; omega)
  have homX : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.chrS (.top t (j + 1)))
      (G.chrT (.top t (j + 1)) * χz * χz⁻¹) (Wl.om (.top t (j + 1))) := by
    rw [mul_inv_cancel_right]; exact homX0
  have hom₁ : IsWeilDatumO Wl.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top (j + 1))) (G.chrS (.top t j) * χz) (G.chrT (.top t j)) (lastAt G Wl t hM j hj vN).s.om₀ := by
    rw [← hS0, ← hT0]; exact (lastAt G Wl t hM j hj vN).s.weil₀
  obtain ⟨omT, homT⟩ := (GlobalTheory.Desc.weil_data_descend D Wl.ψ _ _ _ _ _ (lastAt G Wl t hM j hj vN).weil).1 (G.V (.top (j + 1))) 0 (rowJac G (j + 1) (by omega) 0 (by omega))
  have homT' : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.grid D.R.m D.R.m)) (G.chrS (.top t (j + 1)))
      (G.chrT (.top t (j + 1)) * χz) omT := by
    rw [← hS1, ← hT1]; exact homT
  obtain ⟨omz, homz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1))) Wl.ψ χz
    (G.chrT (.top t j)) hψ hzH homa.hecT hzE homa.resT
  obtain ⟨hzH', hzE'⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χz 1 hzH hzE
  obtain ⟨omz'', homz''⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.top (j + 1))) (pLine D) Wl.ψ
    (G.chrS (.top t (j + 1))) χz⁻¹ hψ homX0.hecS hzH' homX0.resS hzE'
  have hΨ : IsThetaFunO Wl.ψ _ _ ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) := (lastAt G Wl t hM j hj vN).s.weil.om_pres _ _ hΦ₁
  have hΞ : IsThetaFunO Wl.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top (j + 1))) (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁)) :=
    (GlobalTheory.LastRed.val_zero (lastAt G Wl t hM j hj vN).s hΨ).1
  have hΦ₂' : IsThetaFunO Wl.ψ (G.V (.top (j + 1))) (G.V (.grid D.R.m D.R.m))
      (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) := GlobalTheory.RankZeroVac.isThetaFunction_comp_wittExtendByZero _ _ hΦ₂
  obtain ⟨-, key⟩ := GlobalTheory.SeeLastPf.seeLast D Wl.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1)))
    (G.V (.top (j + 1 + 1))) (G.V (.grid D.R.m D.R.m)) (pLine D) (besAt G hM j 0 hj vN).o (topOrthAt G (show D.R.m = j + 1 + 1 by omega))
    lastTau rfl rfl lastTau_gram (G.chrS (.top t j)) χz (G.chrT (.top t j)) (G.chrS (.top t (j + 1)))
    (G.chrT (.top t (j + 1)) * χz) (lastAt G Wl t hM j hj vN).s.om₀ (Wl.om (.top t j)) omz (Wl.om (.top t (j + 1))) omT omz''
    hom₁ homa homz homX homT' homz'' _ _ hΞ hΦ₂'
  have hC := GlobalTheory.LastBiTheta.isBiTheta_lastBi D Wl.ψ hψ (besAt G hM j 0 hj vN).V₀ (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)
    (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.V (.grid D.R.m D.R.m)) (pLine D) (besAt G hM j 0 hj vN).o
    (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau lastTau_gram _ _ hΞ hΦ₂'
  obtain ⟨-, -, hcomm, -⟩ := GlobalTheory.SeeSaw.biAct_all D Wl.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))
    _ _ _ _ (Wl.om (.top t j)) (Wl.om (.top t (j + 1))) homa homX0 _ hC
  have pt : ∀ h' g₀ h₀, omT (g₀, h') (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) 0 *
      (φ h₀ * (lastAt G Wl t hM j hj vN).s.om₀ ((besAt G hM j 0 hj vN).o.emb (h₀, 1), g₀) (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁)) 0) =
      φ h₀ * Wl.om (.top t (j + 1)) (g₀, topEmb G (show D.R.m = j + 1 + 1 by omega) h')
        (fun v => Wl.om (.top t j) (h₀, g₀) (fun u => lastDat Wl hM j hj vN g Φ₁ Φ₂ u v) 0) 0 := by
    intro h' g₀ h₀
    rw [mul_left_comm]
    congr 1
    refine (key h₀ g₀ h').trans ?_
    rw [← topOrthAt_emb]
    exact (hcomm (h₀, g₀) (g₀, _) 0 0).symm
  have inner : ∀ h', (∫ h in (lastAt G Wl t hM j hj vN).s.vW.𝓕, (lastAt G Wl t hM j hj vN).om (h, h') Φ₂ 0 *
      (∫ h₀ in (besAt G hM j 0 hj vN).vA.𝓕, φ h₀ * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, h) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 ∂(besAt G hM j 0 hj vN).vA.μ) ∂(lastAt G Wl t hM j hj vN).s.vW.μ) =
      GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (lastDat Wl hM j hj vN g Φ₁ Φ₂) (topEmb G (show D.R.m = j + 1 + 1 by omega) h') := by
    intro h'
    refine (GlobalTheory.RowVolZero.vol_rankZero G t hM (j + 1) (by omega) (fun h => (lastAt G Wl t hM j hj vN).om (h, h') Φ₂ 0 *
      (∫ h₀ in (besAt G hM j 0 hj vN).vA.𝓕, φ h₀ * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, h) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 ∂(besAt G hM j 0 hj vN).vA.μ)) ?_).trans ?_
    · intro γ hγ x
      have a1 : (lastAt G Wl t hM j hj vN).om (γ * x, h') Φ₂ 0 = (lastAt G Wl t hM j hj vN).om (x, h') Φ₂ 0 := by
        have hm : (lastAt G Wl t hM j hj vN).om (γ * x, h') = (lastAt G Wl t hM j hj vN).om (γ, 1) * (lastAt G Wl t hM j hj vN).om (x, h') := by
          rw [← map_mul]; exact congrArg _ (Prod.ext rfl (one_mul h').symm)
        rw [hm]
        exact (lastAt G Wl t hM j hj vN).weil.om_aut γ hγ 1 (one_mem _) _ ((lastAt G Wl t hM j hj vN).weil.om_pres _ _ hΦ₂)
      have a2 : ∀ h₀, (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, γ * x) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 =
          (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, x) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 := by
        intro h₀
        have hm : (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, γ * x) = (lastAt G Wl t hM j hj vN).s.om (1, γ) * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, x) := by
          rw [← map_mul]; exact congrArg _ (Prod.ext (one_mul _).symm rfl)
        rw [hm]
        exact (lastAt G Wl t hM j hj vN).s.weil.om_aut 1 (one_mem _) γ hγ _ ((lastAt G Wl t hM j hj vN).s.weil.om_pres _ _ hΨ)
      simp only [a1, a2]
    · unfold GlobalTheory.SeeSaw.biLift
      refine integral_congr_ae (Filter.Eventually.of_forall fun g₀ => ?_)
      have e1 : (lastAt G Wl t hM j hj vN).om ((rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀, h') Φ₂ 0 = omT (g₀, h') (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) 0 :=
        GlobalTheory.FinPl.VLast.Transport.weilRep_rankZeroWittEmbedding_valueAtZero D Wl.ψ _ _ _ (rowJac G (j + 1) (by omega) 0 (by omega)) _ _ _ omT (lastAt G Wl t hM j hj vN).weil homT Φ₂ hΦ₂ g₀ h'
      have e2 : ∀ h₀, (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, (rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 =
          (lastAt G Wl t hM j hj vN).s.om₀ ((besAt G hM j 0 hj vN).o.emb (h₀, 1), g₀) (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁)) 0 := fun h₀ =>
        GlobalTheory.FinPl.VLast.Transport.om_flatBF_rankZero D Wl.ψ (besAt G hM j 0 hj vN) (lastAt G Wl t hM j hj vN).J (lastAt G Wl t hM j hj vN).s _ hΨ h₀ g₀
      show (lastAt G Wl t hM j hj vN).om ((rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀, h') Φ₂ 0 * (∫ h₀ in (besAt G hM j 0 hj vN).vA.𝓕,
        φ h₀ * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, (rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 ∂(besAt G hM j 0 hj vN).vA.μ) = _
      rw [e1]
      simp only [e2]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_)
      exact pt h' g₀ h₀
  unfold Last.Q
  refine integral_congr_ae (Filter.Eventually.of_forall fun h' => ?_)
  exact congrArg (F h' * ·) (inner h')

end GlobalTheory.RowChain.LastSeeSawStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedFlipTensorValuesMemCoeffField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest

theorem term_datum_mem_range : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, (ch.S.term t Φ β w).datum X Y ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w X Y
  by_cases h0 : (ch.S.term t Φ β w).datum X Y = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hlc := _root_.GlobalTheory.FlipIntegrand.flatIntegrand_lc_cpt ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w X Y
  have hT := _root_.GlobalTheory.RowTest.Tflip_mem_range ch large₂ F CF b hS hIs hSc hF t Φ hSum w.1 w.2
  have hM := GlobalTheory.T.movedTensorFactor_mem_coeffField ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w _ hT
  show flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) _ X Y ∈ _
  refine _root_.GlobalTheory.LCIntegralField.integral_vars_mem_range (unitVol w.1) (isUnitVol_unitVol w.1) D.what₂.embLL _ hlc.1 hlc.2 fun e => ?_
  simp only [flatIntegrand]
  by_cases hm : moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)
      (fill one_le_sLen X Y e) = 0
  · rw [hm, zero_mul]; exact ⟨0, map_zero _⟩
  obtain ⟨a, ha⟩ := hM (fill one_le_sLen X Y e)
  obtain ⟨c, hc⟩ := hF.phases t Φ β hβ w X Y e h0 hm
  refine ⟨a * c⁻¹, ?_⟩
  rw [map_mul, map_inv₀, ha, hc, AddChar.map_neg_eq_inv, Circle.coe_inv]

end GlobalTheory.RowTest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConjLevelMovesVacuumByCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt resG_compl suppAt_resG isDetAt_detAt resG_one resG_mul actO_actO isHalf_actO)

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem omega_conj_vac_low: ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      W.om (.top t j) (1, (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        (∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he Tm hTm
  change W.om (.top t j) (1, conjPt S j k) (S.Z.vac (.top t j)) = _ • Tm fun x => halfInd e (stdLatO S (.top t j))
    (actO _ _ 1⁻¹ (conjPt S j k)⁻¹ x)
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have he2 : e * e = e := ho.idem
  have hc : e * cA D e = 0 := he.2
  obtain ⟨ε, hε, halg⟩ := _root_.GlobalTheory.IdemSumF.exists_idem_below he
  have hε' : IsIdempotentElem (1 - ε) := hε.one_sub
  have hsplit : (((1 : GA D (G.V (.top j))), conjPt S j k) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) =
      (1, resG _ ε (conjPt S j k)) * (1, resG _ (1 - ε) (conjPt S j k)) := by
    rw [Prod.mk_mul_mk, one_mul, resG_compl _ hε]
  have hdp : DefPair D.R.m (.top t j : Pair T) := by show j + 1 ≤ D.R.m; omega
  have hW := W.om_is (.top t j) (by simp only [Pair.InRange, Node.InRange]; omega)
  have hv := S.Z.vac_is _ hdp
  have hS := S.N.selfDual (X := .top j) (by show j ≤ D.R.m; omega)
  have hT := S.N.selfDual (X := .top (j + 1)) (by show j + 1 ≤ D.R.m; omega)
  have hlaw := GlobalTheory.SplitLinear.law_orth hW hS hT ho hc hv.2.theta hv.2.lat one_ne_zero hTm
    (GlobalTheory.SplitLinear.suppAt_one e _) (suppAt_resG _ hε (conjPt S j k) halg.symm) (isDetAt_detAt he2 _ 1)
    (isDetAt_detAt he2 _ (resG _ ε (conjPt S j k)))
  have hvac : Tm (halfInd e (stdLatO S (.top t j))) = S.Z.vac (.top t j) := by
    have := hTm.vac; rwa [one_smul] at this
  rw [hsplit, map_mul, Module.End.mul_apply, _root_.GlobalTheory.TopLevelInv.vacFix_conjPt_off S hL ht j hj k hk e he ε hε halg]
  conv_lhs => rw [← hvac]
  refine (hlaw (halfInd e (stdLatO S (.top t j))) (isSBHalf_halfInd e _)).trans ?_
  congr 1
  · rw [detAt_one' he2, detAt_resG_eq he2 hc hε halg, GlobalTheory.T.detIdele_conjugatedTopPoint_eq_prod_local S ht j hj k e he]
    unfold GlobalTheory.SplitLinear.fac
    simp only [splitFacO, map_one, inv_one, one_mul]
    rw [_root_.GlobalTheory.TopLevelInv.chrS_top_prod_locIdele G hL j hj]
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    have hm : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1
        (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w))) = 1 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac
      rw [_root_.GlobalTheory.TopLevelInv.absFin_prod_locIdele_unit _ _ (valuation_gdet_kapAt S hj hk), h1, Real.one_rpow, Real.one_rpow, mul_one]
    rw [hm, Complex.ofReal_one, mul_one]
  · congr 1
    funext x
    apply halfInd_congr
    by_cases hx : IsHalf e x
    · have hinv : (conjPt S j k)⁻¹ = resG _ (1 - ε) (conjPt S j k)⁻¹ * (resG _ ε (conjPt S j k))⁻¹ := by
        rw [← resG_inv_eq hε', ← _root_.mul_inv_rev, resG_compl _ hε]
      have key : actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1⁻¹ (conjPt S j k)⁻¹ x =
          actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1⁻¹ (resG _ ε (conjPt S j k))⁻¹ x :=
        calc _ = actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (1 * 1⁻¹)
              (resG _ (1 - ε) (conjPt S j k)⁻¹ * (resG _ ε (conjPt S j k))⁻¹) x := by rw [one_mul, ← hinv]
          _ = actO _ _ 1 (resG _ (1 - ε) (conjPt S j k)⁻¹)
              (actO _ _ 1⁻¹ (resG _ ε (conjPt S j k))⁻¹ x) := (actO_actO _ _ _ _ _).symm
          _ = _ := actO_one_resG_compl he2 hc hε halg _ _ ((isHalf_actO _ _ _).2 hx)
      rw [key]
    · constructor <;> rintro ⟨-, h⟩ <;> exact absurd ((isHalf_actO _ _ _).1 h) hx

end GlobalTheory.TopLevelInv

end
end

