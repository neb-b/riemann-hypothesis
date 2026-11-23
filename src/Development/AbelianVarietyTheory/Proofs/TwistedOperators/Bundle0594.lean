module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainTopPairMovedVectorRowCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section EigTop

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem cart_eq_one_of_posOnb (W : G.Weil) {X : Node} (hX : X.InRange D.R.m) (hP : PosOnb W X) (τ : D.what₂.Tau) :
    W.cart X τ = 1 := by
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hX τ
  rw [hP τ] at h1
  rw [← h1, Matrix.mul_one] at h2
  have hd : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (hP τ)
  calc W.cart X τ = W.cart X τ * W.onb X τ * (W.onb X τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    _ = 1 := by rw [h2, Matrix.mul_nonsing_inv _ hd]

theorem compAt_mt_eq_archM (θ : InfFam D) (V : HSp D) (k : GA D V) (τ : D.what₂.Tau) :
    compAt θ τ (mt V k) = Formalism.L2.Pj.archM V (θ τ) k := by
  have e := GlobalTheory.RealType.realFr_coe θ V 1 k τ
  rw [GlobalTheory.RealType.realFr_one] at e
  rw [show compAt θ τ (mt V k) = ((GlobalTheory.CoefModel.realGL θ V k τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) from rfl, e]
  simp

theorem det_conj_submatrix {a b : ℕ} (h : a = b) {B : Matrix (Fin b) (Fin b) ℂ} (hB : IsUnit B.det)
    (u : Matrix (Fin a) (Fin a) ℂ) :
    (B * u.submatrix (Fin.cast h.symm) (Fin.cast h.symm) * B⁻¹).det = u.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', mul_comm, ← mul_assoc,
    inv_mul_cancel₀ hB.ne_zero, one_mul]
  rfl

end EigTop

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section EigTop2

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem det_compAt_ptTop (W : G.Weil) (μ0 : T) (hL : L.Is μ0) {U : Set T} (N : Std G U)
    (g : Gc D.what₂.Tau (rowSizes D)) (n : Fin (D.R.m + 1)) (τ : D.what₂.Tau) :
    (compAt W.θ τ (mt (G.V (.top n)) (ptTop W g n))).det =
      (rowComp (rowSizes D) g n τ).1.det := by
  induction n using Fin.lastCases with
  | last =>
    show (compAt W.θ τ (mt (G.V (.top D.R.m)) (ptTop W g D.R.m))).det = _
    have hP : PosOnb W (.grid D.R.m D.R.m) :=
      posOnb_of_defNode W μ0 hL (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩
    have hd := fun τ => Matrix.isUnit_det_of_left_inverse (hP τ)
    rw [ptTop_m, kappaTop_apply, compAt_mt_eq_archM]
    have e1 : ∀ (X : Node) (k : GA D (G.V X)), (Formalism.L2.Pj.archM (G.V X) (W.θ τ) k).det =
        ((GlobalTheory.RealType.realAt W.θ N X k τ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).det :=
      fun X k => by rw [GlobalTheory.RealType.realAt, GlobalTheory.RealType.realFr_coe, Matrix.det_units_conj']
    rw [e1, (GlobalTheory.RealType.isBlock_realAt W.θ_is N _ τ).det, mul_one, ← e1, ← compAt_mt_eq_archM]
    have e2 := compAt_kappa_snd g (Fin.last _) hP τ
    erw [e2, det_conj_submatrix (rank_gridM G le_rfl).symm (hd τ)]
    have e : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    erw [e]
    show _ = (Matrix.reindex (finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ)) (finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ))
      (Matrix.fromBlocks (g.2 (Fin.last D.R.m) τ).1 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).det
    rw [Matrix.det_reindex_self]
    exact ((Matrix.det_fromBlocks_zero₂₁ _ _ _).trans (by rw [Matrix.det_one, mul_one]; rfl)).symm
  | cast j =>
    show (compAt W.θ τ (mt (G.V (.top j)) (ptTop W g j))).det = _
    have hP : PosOnb W (.top j) := posOnb_of_defNode W μ0 hL (X := .top j) j.2.le
    rw [ptTop_lt W g j.2, compAt_kappa_fst g j hP τ, det_conj_submatrix (rank_top G j.2.le).symm (Matrix.isUnit_det_of_left_inverse (hP τ))]
    have e : rowComp (rowSizes D) g j.castSucc = g.1 j := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_castSucc (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _ j
    rw [e]

end EigTop2

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section EigTop3

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem movedVec_theta_fock (W : G.Weil) (μ0 : T) (hL : L.Is μ0) {U : Set T} (S : GridChoice W U) (t : T) {j : ℕ}
    (hj : j + 1 ≤ D.R.m) (d : FinDatum G t (.top t j)) (hd : S.Z.HasVec d) :
    IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (movedVec t S d) ∧
      ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.top t j)) (G.pT (.top t j))) W.θ τ (cplxO 1 1) (movedVec t S d) := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := hj
  have hW := W.om_is _ hr
  have hX0 : DefNode D.R.m (.top j) := by show j ≤ D.R.m; omega
  have hX1 : DefNode D.R.m (.top (j + 1)) := hj
  have hc0 := cart_eq_one_of_posOnb W hX0.inRange (posOnb_of_defNode W μ0 hL hX0)
  have hc1 := cart_eq_one_of_posOnb W hX1.inRange (posOnb_of_defNode W μ0 hL hX1)
  obtain ⟨hv1, hv2⟩ := GlobalTheory.FockRealVec.vec_theta_fock W S.Z (p := .top t j) hj d hd
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.top t j)) (G.pT (.top t j))) W.θ τ (cplxO 1 1) (S.Z.vec d) := fun τ => by
    have := hv2 τ
    rwa [show G.cartS W.cart (.top t j) τ = 1 from hc0 τ, show G.onT W.cart (.top t j) τ = 1 from hc1 τ] at this
  refine ⟨hW.om_pres _ _ hv1, fun τ z => ?_⟩
  unfold movedVec
  generalize G.toPair (.top t j) (S.N.u (Pair.top t j).small).1 (S.N.u (Pair.top t j).big).1 = q
  obtain ⟨a, b⟩ := q
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin (G.pT (.top t j)).rank) (Fin (G.pS (.top t j)).rank) ℂ, z = compAt W.θ τ (mt _ b) * z₀ * compAt W.θ τ (mt _ a⁻¹) := by
    refine ⟨compAt W.θ τ (mt _ b⁻¹) * z * compAt W.θ τ (mt _ a), ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  have h0 := congrArg (W.om _ (a, b)) (hv τ z₀)
  rw [GlobalTheory.FockMove.om_annih hW W.θ_is a b τ (by rw [Matrix.one_mul, Matrix.mul_one])
    (by rw [Matrix.one_mul, Matrix.mul_one]) z₀ hv1, map_zero] at h0
  exact h0

theorem cast_half {K : Type} [Field K] [CharZero K] {n : ℕ} (hn : Even n) : (((n / 2 : ℕ) : ℤ) : K) = (n : K) / 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [show (k + k) / 2 = k by omega]
  push_cast
  ring

end EigTop3

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

theorem om_ptTop_movedVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (j : Fin D.R.m)
    (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    W.om (.top t j) (G.toPair (.top t j) (GlobalTheory.RowReal.ptTop W g j) (GlobalTheory.RowReal.ptTop W g (j + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.rowScal (GlobalTheory.RowReal.rowEntries D sc.cGap) j g • movedVec t S d := by
  intro D T L sc G μ0 hL W U S g t j d hd
  have hj : (j : ℕ) + 1 ≤ D.R.m := j.2
  have hr : (Pair.top t (j : ℕ) : Pair T).InRange D.R.m := hj
  have hW := W.om_is _ hr
  have hX0 : DefNode D.R.m (.top j) := j.2.le
  have hX1 : DefNode D.R.m (.top ((j : ℕ) + 1)) := hj
  have hc0 := cart_eq_one_of_posOnb W hX0.inRange (posOnb_of_defNode W μ0 hL hX0)
  have hc1 := cart_eq_one_of_posOnb W hX1.inRange (posOnb_of_defNode W μ0 hL hX1)
  have hS : ∀ τ, IsCartanInv (gramAt D (G.V (.top j)) τ) 1 := fun τ => by
    have := W.cart_is _ hX0.inRange τ
    rwa [hc0 τ] at this
  have hT : ∀ τ, IsCartanInv (gramAt D (G.V (.top ((j : ℕ) + 1))) τ) 1 := fun τ => by
    have := W.cart_is _ hX1.inRange τ
    rwa [hc1 τ] at this
  obtain ⟨hm, hv⟩ := movedVec_theta_fock W μ0 hL S t hj d hd
  have ev0 : Even (G.V (.top j)).rank := by rw [rank_top G j.2.le]; exact even_nR _
  have ev1 : Even (G.V (.top ((j : ℕ) + 1))).rank := by rw [rank_top G hj]; exact even_nR _
  have hχS : G.chrS (.top t j) = L.mu t ((j : ℕ) + 1) := by
    show Formalism.IndefR.Lift.attChr (L.mu t ((j : ℕ) + 1)) L.eta (G.V (.top j)).rank = _
    simp [Formalism.IndefR.Lift.attChr, Nat.not_odd_iff_even.2 ev0]
  have hχT : G.chrT (.top t j) = L.mu t ((j : ℕ) + 1) := by
    show Formalism.IndefR.Lift.attChr (L.mu t ((j : ℕ) + 1)) L.eta (G.V (.top ((j : ℕ) + 1))).rank = _
    simp [Formalism.IndefR.Lift.attChr, Nat.not_odd_iff_even.2 ev1]
  have hexp : ∀ τ, HasInfExp D (L.mu t ((j : ℕ) + 1)) τ (-(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ)) := fun τ => by
    have h := GlobalTheory.GridJoin.ColIt.hasInfExp_mu L hL t j τ
    have e : (((rowEntries D sc.cGap τ).e j : ℤ) : ℚ) = (D.hc τ).e j := by
      show (((num D sc.cGap τ).e ((j : ℕ) + 1) : ℤ) : ℚ) = _
      exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).e_int ⟨j, j.2⟩
    rwa [e]
  have key := GlobalTheory.VacuumCharacter.vacuum_character D W.ψ W.θ (G.V (.top j)) (G.V (.top ((j : ℕ) + 1)))
    (G.chrS (.top t j)) (G.chrT (.top t j)) (W.om (.top t j)) hW W.θ_is (hX0.sigOK G) (hX1.sigOK G) (fun _ => 1) hS hT
    (fun τ => -(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ)) (fun τ => -(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ))
    (fun τ => by rw [hχS]; exact hexp τ) (fun τ => by rw [hχT]; exact hexp τ)
    (fun τ => -(rowEntries D sc.cGap τ).e j + ((rowSizes D).nR j.castSucc / 2 : ℕ))
    (fun τ => -(rowEntries D sc.cGap τ).e j - ((rowSizes D).nR j.castSucc / 2 : ℕ))
    (fun τ => (rowEntries D sc.cGap τ).e j - ((rowSizes D).nR j.succ / 2 : ℕ))
    (fun τ => by
      rw [Int.cast_add, Int.cast_neg, Fin.val_castSucc, cast_half (even_nR (S := rowSizes D) j), rank_top G j.2.le])
    (fun τ => by
      rw [Int.cast_sub, Int.cast_neg, Fin.val_castSucc, cast_half (even_nR (S := rowSizes D) j), rank_top G j.2.le])
    (fun τ => by
      rw [Matrix.trace_one, Fintype.card_fin, rank_top G hj, Int.cast_sub, Fin.val_succ,
        cast_half (even_nR (S := rowSizes D) ((j : ℕ) + 1))]
      push_cast
      ring)
    (movedVec t S d) hm hv (ptTop W g j) (ptTop_mem W g j) (ptTop W g ((j : ℕ) + 1)) (ptTop_mem W g _)
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
  rw [show G.toPair (.top t j) (ptTop W g j) (ptTop W g ((j : ℕ) + 1)) = (ptTop W g j, ptTop W g ((j : ℕ) + 1)) from rfl, key]
  congr 1
  clear key hexp hχS hχT ev0 ev1 hm hv hS hT hc0 hc1 hW hr hd
  have a1 : (1 / 2 : ℂ) • ((1 : Matrix (Fin (G.V (.top ((j : ℕ) + 1))).rank) (Fin (G.V (.top ((j : ℕ) + 1))).rank) ℂ) + 1) = 1 := by
    module
  simp only [a1, sub_self, smul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, Matrix.det_one, one_zpow, mul_one]
  have hg : ∀ τ, (compAt W.θ τ (mt (G.V (.top j)) (ptTop W g j))).det = (rowComp (rowSizes D) g j.castSucc τ).1.det :=
    fun τ => det_compAt_ptTop W μ0 hL S.N g j.castSucc τ
  have hh : ∀ τ, (compAt W.θ τ (mt (G.V (.top ((j : ℕ) + 1))) (ptTop W g ((j : ℕ) + 1)))).det =
      (rowComp (rowSizes D) g j.succ τ).1.det :=
    fun τ => det_compAt_ptTop W μ0 hL S.N g j.succ τ
  simp only [hg, hh]
  simp [rowScal, detChar, detU, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => mul_comm _ _

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdealMembershipCriterion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharComb

variable {D : D7}

theorem pairA_zero_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  exact Prod.ext (zero_mul _) rfl

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) :
    α * β ∈ intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem complId_mul {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x y : AE D} (hx : x ∈ complId 𝔞)
    (hy : y ∈ complId 𝔟) : x * y ∈ complId (𝔞 * 𝔟) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, a, ha, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, b, hb, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_zero_mul]
      exact tmul_mem_complId (intAf_mul hα hβ) (FractionalIdeal.mul_mem_mul ha hb)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem infPart_of_mem {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : AE D} (hx : x ∈ complId 𝔠) :
    infPart D x = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, a, -, rfl⟩ := hx
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] a = 0
    exact TensorProduct.zero_tmul _ _
  | zero => exact map_zero _
  | add x z _ _ hx hz => rw [RingHom.map_add (f := _), hx, hz, add_zero]
  | neg x _ hx => rw [RingHom.map_neg, hx, neg_zero]

def finId (𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : AddSubgroup (EAf D) :=
  (complId 𝔠).map (toEAf D).toAddMonoidHom

theorem finId_mul {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x y : EAf D} (hx : x ∈ finId 𝔞)
    (hy : y ∈ finId 𝔟) : x * y ∈ finId (𝔞 * 𝔟) := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  exact ⟨x₀ * y₀, complId_mul hx₀ hy₀, map_mul (toEAf D) x₀ y₀⟩

theorem tmul_one_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {a : D.host.E} (ha : a ∈ 𝔠) :
    a ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ finId 𝔠 :=
  ⟨_, tmul_mem_complId one_mem_intAf ha, rfl⟩

theorem int_mem_finId_one {z : EAf D} (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    z ∈ finId (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  induction hz using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨b, hb⟩ := b
      exact tmul_one_mem_finId ((FractionalIdeal.mem_one_iff _).2 hb)
    · exact ⟨_, tmul_mem_complId y.2 (FractionalIdeal.one_mem_one _), rfl⟩
  | zero => exact zero_mem _
  | one => exact tmul_one_mem_finId (FractionalIdeal.one_mem_one _)
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy => simpa using finId_mul hx hy

theorem idS_mem_finId (𝔪 : Ideal (𝓞 D.host.E)) {t : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (ht : t ∈ Formalism.L2.DIV.idS D.host.F 𝔪) :
    (t : EAf D) ∈ finId ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe]
    exact tmul_one_mem_finId ((FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => rw [Subring.coe_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul]
    simpa using finId_mul (int_mem_finId_one c.2) hx

theorem idem_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {e : AE D} {Q : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt e Q) {a : D.host.E} (ha : a ∈ 𝔠)
    (hv : Valued.v (algebraMap D.host.E (Kw Q) a) = 1) : toEAf D e ∈ finId 𝔠 := by
  have ha0 : a ≠ 0 := fun h => by rw [h, map_zero, map_zero] at hv; exact zero_ne_one hv
  obtain ⟨h1, h2⟩ := GlobalTheory.StdFrames.cpt_of_isIdemAt he
  have hu : toEAf D e * (a⁻¹ ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine (GlobalTheory.StdFrames.mem_OA_iff _).2 fun Q' => ?_
    rw [map_mul, GlobalTheory.FunObj.Comparison₂.cpt_tmul]
    by_cases hQ : Q' = Q
    · subst hQ
      rw [h1, one_mul, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, hv, inv_one]
    · rw [h2 Q' hQ, zero_mul]
      exact zero_mem _
  have e1 : toEAf D e = (toEAf D e * (a⁻¹ ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F))) *
      (a ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) := by
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ ha0, one_mul,
      Algebra.TensorProduct.one_def.symm, mul_one]
  rw [e1]
  simpa using finId_mul (int_mem_finId_one hu) (tmul_one_mem_finId ha)

theorem toEAf_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : AE D} (hx : x ∈ complId 𝔠) :
    toEAf D x ∈ finId 𝔠 := ⟨x, hx, rfl⟩

theorem ring_key {R : Type*} [CommRing R] (e c : R) : c = e * (e * c) + ((1 + e) * (1 - e)) * c := by ring

theorem mem_complId_of_finId {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {c : AE D} (hc : c ∈ complId 𝔞)
    (h : toEAf D c ∈ finId 𝔟) : c ∈ complId 𝔟 := by
  obtain ⟨z, hz, hze⟩ := h
  have hze' : toEAf D z = toEAf D c := hze
  have hzc : z = c := GlobalTheory.DepthFix.ext_cpt (by rw [infPart_of_mem hz, infPart_of_mem hc])
    fun Q => by rw [hze']
  exact hzc ▸ hz

theorem core {𝔞 𝔟 𝔪 𝔡 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hid : 𝔪 * 𝔡 = 𝔞 * 𝔟) {e c : EAf D}
    (he : e ∈ finId 𝔞) (hec : e * c ∈ finId 𝔟) (hm : (1 + e) * (1 - e) ∈ finId 𝔪) (hc : c ∈ finId 𝔡) :
    c ∈ finId (𝔞 * 𝔟) := by
  have h3 := finId_mul hm hc
  rw [hid] at h3
  have h4 := add_mem (finId_mul he hec) h3
  rwa [← ring_key e c] at h4

theorem ideal_key {M A B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hM : M ≠ 0) :
    M * (A * (B * M⁻¹)) = A * B := by
  calc _ = A * B * (M * M⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hM, mul_one]

theorem mem_complId_AA_AAbar : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 →
    ∀ {sc : Consts} (G : GridData L sc) (c : AE D), c ∈ complId (D.host.AA * G.pl.stAbar sc) →
    (∀ e, IsIdemSum e G.pl.W0 → e * c ∈ complId D.host.AAbar) → c ∈ complId (D.host.AA * D.host.AAbar) := by
  classical
  intro D hq T L μ0 hL sc G c hc hec
  obtain ⟨e, he⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have h1 := hec e he
  obtain ⟨-, heO, t, ht, hte⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props e G.pl.W0
    (fun Q => G.pl.depth sc (Q.under (𝓞 D.host.F))) he
  have hprod : (∏ Q ∈ G.pl.W0, Q.asIdeal ^ G.pl.depth sc (Q.under (𝓞 D.host.F))) = G.pl.modul sc := by
    unfold Places.W0 Places.modul
    rw [Finset.prod_image fun v hv v' hv' h =>
      (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))]
    exact Finset.prod_congr rfl fun v hv => by rw [G.pl.under_w hv]
  rw [hprod] at ht

  have heA : toEAf D e ∈ finId D.host.AA := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := id he
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show toEAf D (∑ Q ∈ G.pl.W0, es Q) = ∑ Q ∈ G.pl.W0, toEAf D (es Q) from
      map_sum (toEAf D).toAddMonoidHom (fun Q => es Q) G.pl.W0]
    refine sum_mem fun Q hQ => ?_
    obtain ⟨a, ha, hv⟩ := GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hq hL G Q hQ
    exact idem_mem_finId (hes Q hQ) ha hv

  have ht2 : ((⟨1 + toEAf D e, add_mem (one_mem _) heO⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * t) ∈
      Formalism.L2.DIV.idS D.host.F (G.pl.modul sc) := Ideal.mul_mem_left _ _ ht
  have hM : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hid : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
      (D.host.AA * G.pl.stAbar sc) = D.host.AA * D.host.AAbar := ideal_key hM
  have hm := idS_mem_finId _ ht2
  rw [Subring.coe_mul, hte] at hm
  have h1f := toEAf_mem_finId h1
  rw [RingHom.map_mul] at h1f
  exact mem_complId_of_finId hc (core hid heA h1f hm (toEAf_mem_finId hc))

end GlobalTheory.XCharComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteNodeCartanOrthonormalBasisAllPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

section DefOnb

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem gramAt_negSp (V : HSp D) (ρ : D.what₂.Tau) : gramAt D (negSp V) ρ = -gramAt D V ρ := by
  unfold gramAt
  rw [negSp_gram]
  exact Matrix.map_neg _ (map_neg (tauE D ρ)) _

theorem isCartanInv_neg {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : IsCartanInv (-G) (-s) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [neg_mul_neg, h1], ?_, ?_⟩
  · rw [Matrix.conjTranspose_neg, neg_mul_neg, Matrix.mul_neg, h2]
  · rw [neg_mul_neg]; exact h3

theorem defNode_cart_onb {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (X : Node) (hX : DefNode D.R.m X) (ρ : D.what₂.Tau) :
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 := by
  have hC := W.cart_is X hX.inRange ρ
  have hP : (W.onb X ρ)ᴴ * gramAt D (G.V X) ρ * W.onb X ρ = 1 := posOnb_of_defNode W μ0 hL hX ρ
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hX.inRange ρ
  have hJ : Formalism.REAL.Jm ε = 1 := h1.symm.trans hP
  rw [hJ, Matrix.mul_one] at h2
  have hn : gramAt D (negSp (G.V X)) ρ = -gramAt D (G.V X) ρ := gramAt_negSp _ _
  refine ⟨hC, ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩, ?_, ⟨fun _ => -1, fun a => Or.inr ⟨rfl, Nat.zero_le _⟩, ?_, ?_⟩⟩
  · rw [hP]; simp [Matrix.diagonal_one]
  · rw [h2]; simp [Matrix.diagonal_one]
  · rw [hn]; exact isCartanInv_neg hC
  · rw [hn, Matrix.mul_neg, Matrix.neg_mul, hP]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  · rw [Matrix.neg_mul, h2]
    ext i j
    simp [Matrix.mul_diagonal]

theorem defNode_cart_onb_all : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (X : Node), DefNode D.R.m X → ∀ ρ,
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 :=
  fun hL W X hX ρ => defNode_cart_onb hL W X hX ρ

end DefOnb

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepThetaLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.LastStepLift

theorem exists_lastStep_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels →
    R.IsChainW → R.ex_ioX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hfam hmod hc
  have hIt : R.chain_ItX := hc.ItX.1 (_root_.GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner D G Pl0 T A Ks R hlev hfam hmod hc)
  obtain ⟨io, hio⟩ := GlobalTheory.T.exists_multiplicityLift_lastChainStep D G Pl0 T A Ks R hlev hfam hmod hc.ωX hc.vX hc.ptX hIt
  exact fun t => ⟨io t, hio t⟩

end GlobalTheory.Twist.LastStepLift
end

