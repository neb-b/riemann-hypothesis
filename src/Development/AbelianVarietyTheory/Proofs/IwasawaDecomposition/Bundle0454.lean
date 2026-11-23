module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismsNearSameAdelicCongruent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.AdTieNear

theorem entries_le_of_add_mul {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ))) {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) K) (c : WithZero (Multiplicative ℤ)) (hA : ∀ r s, v (A r s) < 1)
    (h : ∀ r s, v ((D + A * D) r s) ≤ c) (r s : Fin n) : v (D r s) ≤ c := by
  obtain ⟨p, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v (D p.1 p.2)) ⟨(r, s), Finset.mem_univ _⟩
  refine (hmax (r, s) (Finset.mem_univ _)).trans ?_
  by_cases hμ : v (D p.1 p.2) = 0
  · rw [hμ]; exact zero_le'
  have hlt : v ((A * D) p.1 p.2) < v (D p.1 p.2) := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ hμ fun k _ => ?_
    rw [map_mul]
    calc v (A p.1 k) * v (D k p.2) ≤ v (A p.1 k) * v (D p.1 p.2) :=
          mul_le_mul_right (hmax (k, p.2) (Finset.mem_univ _)) _
      _ < 1 * v (D p.1 p.2) := mul_lt_mul_of_pos_right (hA p.1 k) (zero_lt_iff.2 hμ)
      _ = v (D p.1 p.2) := one_mul _
  have e := Valuation.map_add_eq_of_lt_left v hlt
  rw [← e, ← Matrix.add_apply]
  exact h p.1 p.2

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_ratA {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (G : GL (Fin n) E) (r s : Fin n) :
    adAt F P ((GlobalTheory.TwU.ratA F G : GL (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((G : Matrix (Fin n) (Fin n) E) r s) := by
  exact adAt_inclE F P _

theorem congE_of_near (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (d d' : ℕ) (hd' : 1 ≤ d') (hdd : d' ≤ d)
    (x : GL (Fin n) (AfE F E)) (g g' : Sp E n ≃ₗ[E] Sp E n) (G G' : GL (Fin n) E)
    (hG : ∀ w, (G : Matrix (Fin n) (Fin n) E) *ᵥ w = g w) (hG' : ∀ w, (G' : Matrix (Fin n) (Fin n) E) *ᵥ w = g' w)
    (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    (hy : ∀ r s, Valued.v (adAt F P (((x⁻¹ * GlobalTheory.TwU.ratA F G : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)
      - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(d : ℤ)))
    (hy' : ∀ r s, Valued.v (adAt F P (((x⁻¹ * GlobalTheory.TwU.ratA F G' : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)
      - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(d' : ℤ))) :
    CongE P d' g' g := by
  set φ := adAt F P
  set y := x⁻¹ * GlobalTheory.TwU.ratA F G
  set y' := x⁻¹ * GlobalTheory.TwU.ratA F G'
  set H : GL (Fin n) E := G⁻¹ * G'
  have hyH : y * GlobalTheory.TwU.ratA F H = y' := by
    simp only [y, y', H, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  set Y : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (y : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  set Y' : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (y' : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  set R : Matrix (Fin n) (Fin n) (P.adicCompletion E) := ((GlobalTheory.TwU.ratA F H : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  have hYR : Y * R = Y' := by
    simp only [Y, Y', R, ← Matrix.map_mul, ← Units.val_mul, hyH]
  have hdA : ∀ r s, Valued.v ((Y - 1) r s) < 1 := fun r s => by
    refine lt_of_le_of_lt (hy r s) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hsum : ∀ r s, Valued.v (((R - 1) + (Y - 1) * (R - 1)) r s) ≤ WithZero.exp (-(d' : ℤ)) := fun r s => by
    have e : (R - 1) + (Y - 1) * (R - 1) = (Y' - 1) - (Y - 1) := by
      rw [← hYR]; noncomm_ring
    rw [e, Matrix.sub_apply]
    refine Valuation.map_sub_le _ (hy' r s) ((hy r s).trans ?_)
    rw [WithZero.exp_le_exp]; omega
  have hD := entries_le_of_add_mul Valued.v (Y - 1) (R - 1) _ hdA hsum

  have hH : ∀ r s, Valued.v (algebraMap E (P.adicCompletion E) (((H : Matrix (Fin n) (Fin n) E) - 1) r s)) ≤ WithZero.exp (-(d' : ℤ)) := by
    intro r s
    have e : (R - 1) r s = algebraMap E (P.adicCompletion E) (((H : Matrix (Fin n) (Fin n) E) - 1) r s) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
      simp only [R, Matrix.map_apply, φ, adAt_ratA]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← e]; exact hD r s
  intro w hw
  have hHw : g ((H : Matrix (Fin n) (Fin n) E) *ᵥ w) = g' w := by
    rw [← hG, Matrix.mulVec_mulVec, ← Units.val_mul, ← hG']
    simp only [H, mul_inv_cancel_left]
  have e : (((qOf P : ℕ) : E) ^ d')⁻¹ • (g' w - g w) =
      g ((((qOf P : ℕ) : E) ^ d')⁻¹ • (((H : Matrix (Fin n) (Fin n) E) - 1) *ᵥ w)) := by
    rw [map_smul, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, hHw]
  rw [e]
  refine (hg _).2 ?_
  rw [GlobalTheory.Mem.ColAd.mem_stdAt_val] at hw ⊢
  intro l
  have hs : Valued.v (algebraMap E (P.adicCompletion E) ((((H : Matrix (Fin n) (Fin n) E) - 1) *ᵥ w) l)) ≤ WithZero.exp (-(d' : ℤ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul, map_mul]
    calc _ ≤ WithZero.exp (-(d' : ℤ)) * 1 := mul_le_mul' (hH l k) (hw k)
      _ = _ := mul_one _
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, map_inv₀, map_inv₀, map_pow, map_pow, map_natCast, hq]
  calc _ ≤ (WithZero.exp (-1 : ℤ) ^ d')⁻¹ * WithZero.exp (-(d' : ℤ)) := mul_le_mul_right hs _
    _ = 1 := by
      rw [← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
      simp

end Gen

end GlobalTheory.Mem.Col2.AdT.AdTieNear

namespace GlobalTheory.Mem.Col2.AdT.AdTieNear


set_option maxHeartbeats 800000 in
theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → 1 ≤ dep' P → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' → CongE P.1 (dep' P) g' g := by
  intro B X I hOk l Z a i fb dep dep' P κ g g' hg h1 hdd hF hF'
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hF hF'
  have hq := (_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a ((I.rec7 l Z).R.N i) 0 P 1).2.1
  have hy := (_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a _ (dep P) P _).2.2.1 hF
  have hy' := (_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a _ (dep' P) P _).2.2.1 hF'
  exact congE_of_near (F := B.host.F) P.1 (dep P) (dep' P) h1 hdd _ g g'
    (GlobalTheory.TwU.seamGL (sm I l Z) g) (GlobalTheory.TwU.seamGL (sm I l Z) g')
    (fun w => GlobalTheory.TwU.seamGL_mulVec (sm I l Z) g w) (fun w => GlobalTheory.TwU.seamGL_mulVec (sm I l Z) g' w)
    hg hq hy hy'

end GlobalTheory.Mem.Col2.AdT.AdTieNear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEmbeddingAtOrbitPositionEqInduced
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

theorem splitPlace_embedding_at_orbitPosition_eq_induced : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (q : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' q)) (x : (w.D Z).host.E),
        ((w.D Z).gat u v hg).P.ι q ((((w.D Z).gat u v hg).P.σ q ^ s.val) (GlobalTheory.Mem.Top.KerOne.iw0 t.full.1.g u v hg q x)) =
          t.cmp.embW u v hg (tauLL (w.D Z) (t.Gt.gat_pos u v hg ⟨q, s⟩) (if s.val % 2 = 1 then (w.D Z).host.conj x else x)) := by
  intro K B f T w _ _ _ Z t _ _ _ _ _ _ _ _ _ _ _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  intro q s x
  have h := (t.g.cmp.tie u v hg).pos_emb q s x
  have key : ∀ (X : Formalism.L2.Herm.Herm0 (w.D Z)) (Bm : GL (Fin (w.D Z).R.k) (w.D Z).host.E), X = t.full.1.to0 →
      (Formalism.L2.G.Cmp.locAt X u v hg Bm).iw q x = iw0 t.full.1.g u v hg q x := by
    rintro X Bm rfl; rfl
  rw [key _ _ t.herm_eq] at h
  rw [← h]
  have h3 : Formalism.L2.Forms.sigD (w.D Z) x = (w.D Z).host.conj x := Formalism.BasicNotions.bridge_star_holds (w.D Z).R (w.D Z).host x
  rw [h3]
  show _ = (t.cmp.embW u v hg) (Formalism.L2.G.Cmp.tEL (w.D Z) _ _)
  congr 2
  by_cases hs : s.val % 2 = 1
  · have : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
    simp [hs, this]
  · have : Even s.val := by rw [Nat.even_iff]; omega
    simp [hs, this]

end GlobalTheory.Mem.Top.KerOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGroupCharacterInverseTypeAtLifts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT

section Split

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S Q : Finset (HeightOneSpectrum (𝓞 E))}


open Classical in
def compVal (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) (p : HeightOneSpectrum (𝓞 E)) : Kˣ :=
  if h : p ∈ S then (Λ ⟨p, h⟩).lam ⟨k1.1 ⟨p, h⟩, k1.2 _ (Set.mem_univ _)⟩
  else if h' : p ∈ Q then (Θ ⟨p, h'⟩).lam ⟨k2.1 ⟨p, h'⟩, k2.2 _ (Set.mem_univ _)⟩ else 1

theorem compVal_left (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) {p : HeightOneSpectrum (𝓞 E)} (h : p ∈ S) :
    compVal Λ Θ k1 k2 p = (Λ ⟨p, h⟩).lam ⟨k1.1 ⟨p, h⟩, k1.2 _ (Set.mem_univ _)⟩ := by
  unfold compVal
  rw [dif_pos h]

theorem compVal_right (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) {p : HeightOneSpectrum (𝓞 E)} (h : p ∉ S)
    (h' : p ∈ Q) : compVal Λ Θ k1 k2 p = (Θ ⟨p, h'⟩).lam ⟨k2.1 ⟨p, h'⟩, k2.2 _ (Set.mem_univ _)⟩ := by
  unfold compVal
  rw [dif_neg h, dif_pos h']


open Classical in
theorem prod_compVal (hd : Disjoint S Q) (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) :
    ∏ p ∈ S ∪ Q, compVal Λ Θ k1 k2 p = Λ.chr k1 * Θ.chr k2 := by
  have e1 : Λ.chr k1 = _ := piChar_apply (fun w => (Λ w).H) (fun w => (Λ w).lam) k1
  have e2 : Θ.chr k2 = _ := piChar_apply (fun w => (Θ w).H) (fun w => (Θ w).lam) k2
  rw [e1, e2, Finset.prod_union hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort Q]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
  · exact dif_pos w.2
  · exact (dif_neg (Finset.disjoint_right.1 hd w.2)).trans (dif_pos w.2)

end Split
end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

section Cong

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem congE_mul_one {P : HeightOneSpectrum (𝓞 E)} {c : ℕ} {k g g' : Sp E n ≃ₗ[E] Sp E n}
    (hk : k ∈ GLint E n P) (hkg : k * g' = 1) (h : CongE P c g g') : CongE P c (k * g) 1 := by
  intro x hx
  have e1 : (k * g) x - (1 : Sp E n ≃ₗ[E] Sp E n) x = k (g x - g' x) := by
    rw [map_sub, ← LinearEquiv.mul_apply k g', hkg]
    rfl
  rw [e1, ← map_smul]
  exact (hk _).2 (h x hx)

end Cong
end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

variable {B : Base} {X : PreX B.toPre}

theorem chiInv_at_type (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (al : (I.idx a).β i) (P : SBof I a)
    (hP : P.1 ∈ (B.primes X).vGs) (gP g'P : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (r : AutY B.fields B.R i)
    (hr : r ∈ Loc.Cbe (Jat (Pr := B.primes X) (I.cst a).sharp i P.1) ((I.idx a).h i al P))
    (hrx : ∀ x, r (Loc.inX B.fields.E (B.R.N i) (cOf B.R i) x) = Loc.inX B.fields.E (B.R.N i) (cOf B.R i) (gP x))
    (κw : GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ P.1.asIdeal)) (hκw : κw ∈ (((I.idx a).levG i al) ⟨P.1, hP⟩).H)
    (hred' : ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g'P x) = (κw⁻¹).1.mulVec (redV P.1 x))
    (hcong : CongE P.1 ((I.cst a).D P) gP g'P) :
    chiInv I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) r =
      (((((I.idx a).levG i al) ⟨P.1, hP⟩).lam ⟨κw, hκw⟩ : B.fields.Kˣ) : B.fields.K)⁻¹ := by
  have hL := hOk.idx_ok a
  have hD : (I.cst a).D P = 1 := hL.depthG P hP
  have hred : ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (gP x) = (κw⁻¹).1.mulVec (redV P.1 x) := by
    intro x hx
    rw [← hred' x hx]
    have h1 := (mem_localization_standardLattice _ _).1 (hcong x hx)
    rw [hD, pow_one] at h1
    have hq0 : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
    funext l
    have e1 : gP x l = g'P x l + (qOf P.1 : B.fields.E) * (((qOf P.1 : ℕ) : B.fields.E)⁻¹ • (gP x - g'P x)) l := by
      rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      field_simp
      ring
    show redP P.1 (gP x l) = redP P.1 (g'P x l)
    rw [e1]
    exact GlobalTheory.LastSteps.redP_add_q (h1 l)
  have hc := hL.chrG i al ⟨P.1, hP⟩ (⟨κw, hκw⟩)⁻¹ gP r hr hrx hred
  exact hc.symm.trans ((congrArg Units.val (map_inv (((I.idx a).levG i al) ⟨P.1, hP⟩).lam _)).trans (Units.val_inv_eq_inv_val _))

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

variable {B : Base} {X : PreX B.toPre}

theorem chiInv_at_twist (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (al : (I.idx a).β i) (P : SBof I a)
    (hQ : P.1 ∈ I.Q a) (gP g'P : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (r : AutY B.fields B.R i)
    (hr : r ∈ Loc.Cbe (Jat (Pr := B.primes X) (I.cst a).sharp i P.1) ((I.idx a).h i al P))
    (hrx : ∀ x, r (Loc.inX B.fields.E (B.R.N i) (cOf B.R i) x) = Loc.inX B.fields.E (B.R.N i) (cOf B.R i) (gP x))
    (κQ : ↥(GLint B.fields.E (B.R.N i) P.1)) (hκQ : κQ ∈ (((I.idx a).levQ i al) ⟨P.1, hQ⟩).H)
    (hg' : g'P = (κQ⁻¹).1) (hcong : CongE P.1 ((I.cst a).D P) gP g'P) :
    chiInv I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) r =
      (((((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨κQ, hκQ⟩ : B.fields.Kˣ) : B.fields.K)⁻¹ := by
  have hL := hOk.idx_ok a
  have hg : gP ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp i P.1 ((I.idx a).h i al P) := ⟨r, hr, hrx⟩
  let gI : ↥(GLint B.fields.E (B.R.N i) P.1) := ⟨gP, hL.int i al P hg⟩
  have hH : gI ∈ (((I.idx a).levQ i al) ⟨P.1, hQ⟩).H := by
    rw [hL.grpQ i al ⟨P.1, hQ⟩]
    exact Subgroup.mem_subgroupOf.2 hg
  have hc := hL.chrQ i al ⟨P.1, hQ⟩ ⟨gI, hH⟩ r hr hrx
  have hkg : κQ.1 * g'P = 1 := by
    rw [hg']
    exact congrArg Subtype.val (mul_inv_cancel κQ)
  have hcd : CongE P.1 ((I.cst a).D P) (κQ * gI).1 1 := congE_mul_one (g := gP) κQ.2 hkg hcong
  obtain ⟨hdH, hdl⟩ := levQ_deep I hOk a i hi al P hQ (κQ * gI) hcd
  have e2 : (⟨gI, hH⟩ : ↥(((I.idx a).levQ i al) ⟨P.1, hQ⟩).H) = (⟨κQ, hκQ⟩)⁻¹ * ⟨κQ * gI, hdH⟩ :=
    Subtype.ext (by show gI = κQ⁻¹ * (κQ * gI); group)
  have h4 : (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ((⟨κQ, hκQ⟩)⁻¹ * ⟨κQ * gI, hdH⟩) = ((((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨κQ, hκQ⟩)⁻¹ :=
    ((map_mul (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam _ _).trans ((congrArg _ hdl).trans (mul_one _))).trans (map_inv (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam _)
  exact hc.symm.trans ((congrArg Units.val ((congrArg (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam e2).trans h4)).trans (Units.val_inv_eq_inv_val _))

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT


open Classical in
theorem chr_mul_prod_midAt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, MidAt I hi b P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 ((I.cst a).D P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  intro B X I hOk u a i hi b κ g g' z H
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al hi := ⟨_, (Idx.of_get b hi hi).symm⟩
  let k1 : ↥((I.idx a).levG i al).grp := κ.2.1
  let k2 : ↥((I.idx a).levQ i al).grp := κ.2.2
  have e : (((I.stp u a i).chr (Idx.of al hi) κ : B.fields.Kˣ) : B.fields.K) =
      ((((I.idx a).levG i al).chr k1 * ((I.idx a).levQ i al).chr k2 : B.fields.Kˣ) : B.fields.K) := rfl
  rw [e]
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_right.2 fun {P} hP => GlobalTheory.Mem.Col2.TC.Q_notMem_of_ok hOk a P hP
  have hprod : ∏ P : SBof I a, compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2 P.1 =
      ((I.idx a).levG i al).chr k1 * ((I.idx a).levQ i al).chr k2 := by
    rw [Finset.prod_coe_sort (SBof I a) (compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2)]
    exact prod_compVal hd _ _ k1 k2
  have hz : ∀ P : SBof I a, z P = ((compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2 P.1 : B.fields.Kˣ) : B.fields.K)⁻¹ := by
    intro P
    obtain ⟨⟨r, hr, hrx, hzr⟩, hlift, hcong⟩ := H P
    rw [hzr]
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · refine (chiInv_at_type I hOk a i al P hP (g P) (g' P) r hr hrx (k1.1 ⟨P.1, hP⟩) (k1.2 _ (Set.mem_univ _))
        (hlift.2.1 hP) hcong).trans ?_
      rw [compVal_left _ _ k1 k2 hP]
    · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      refine (chiInv_at_twist I hOk a i hi al P hQ (g P) (g' P) r hr hrx (k2.1 ⟨P.1, hQ⟩) (k2.2 _ (Set.mem_univ _))
        (hlift.2.2 hQ) hcong).trans ?_
      exact congrArg (fun x : B.fields.Kˣ => (x : B.fields.K)⁻¹) (compVal_right _ _ k1 k2 hP hQ).symm
  rw [← hprod, Finset.prod_congr rfl fun P _ => hz P, Units.coe_prod, Finset.prod_inv_distrib]
  exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.2 fun P _ => Units.ne_zero _)

end GlobalTheory.Mem.Col2.AdT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaAutomorphicWeilDataPreservedDivisionLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Top.Bl.ThTTr

open Formalism.L2.Theta Formalism.L2.JoinChr
open scoped TensorProduct
open Formalism.BasicNotions.TH (tauE)

section

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt)
  (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

abbrev thTrZ (X : ThetaX (w.D Z)) : ThetaX (w.D (setDivZ Z N h)) := { X with }

theorem isAutFun_tr {V : TH.HSp (w.D Z)} {φ : GA (w.D Z) V → ℂ} :
    IsAutFun (D := w.D Z) V φ ↔ IsAutFun (D := w.D (setDivZ Z N h)) V φ :=
  ⟨fun x => ⟨x.left, x.level, x.cont⟩, fun x => ⟨x.left, x.level, x.cont⟩⟩

theorem isAutFunSm_tr {θ : (w.D Z).what₂.Tau → (GlobalTheoryTheory.GenusMassVolumes.Ainf (w.D Z).host.F ⊗[(w.D Z).host.F] (w.D Z).host.E →+* ℂ)} {V : TH.HSp (w.D Z)}
    {φ : GA (w.D Z) V → ℂ} : IsAutFunSm (D := w.D Z) θ V φ ↔ IsAutFunSm (D := w.D (setDivZ Z N h)) θ V φ :=
  ⟨fun x => ⟨(isAutFun_tr w Z N h).1 x.toIsAutFun, x.smooth, x.zfin, x.growth⟩,
   fun x => ⟨(isAutFun_tr w Z N h).2 x.toIsAutFun, x.smooth, x.zfin, x.growth⟩⟩

theorem isThetaFun_tr {ψ : AddChar (GlobalTheoryTheory.GenusMassVolumes.AF (w.D Z).host.F) ℂ} {V W : TH.HSp (w.D Z)} {f : WA V W → ℂ} :
    IsThetaFun (D := w.D Z) ψ V W f ↔ IsThetaFun (D := w.D (setDivZ Z N h)) ψ V W f :=
  ⟨fun x => ⟨x.quasi, x.level, x.cont, x.smooth⟩, fun x => ⟨x.quasi, x.level, x.cont, x.smooth⟩⟩

theorem isPolFock_tr {ψ : AddChar (GlobalTheoryTheory.GenusMassVolumes.AF (w.D Z).host.F) ℂ}
    {θ : (w.D Z).what₂.Tau → (GlobalTheoryTheory.GenusMassVolumes.Ainf (w.D Z).host.F ⊗[(w.D Z).host.F] (w.D Z).host.E →+* ℂ)} {V W : TH.HSp (w.D Z)}
    {A : ∀ τ : (w.D Z).what₂.Tau, Matrix (Fin (V.sig (tauE (w.D Z) τ)).1 ⊕ Fin (V.sig (tauE (w.D Z) τ)).2) (Fin V.rank) ℂ}
    {B : ∀ τ : (w.D Z).what₂.Tau, Matrix (Fin (W.sig (tauE (w.D Z) τ)).1 ⊕ Fin (W.sig (tauE (w.D Z) τ)).2) (Fin W.rank) ℂ}
    {f : WA V W → ℂ} :
    IsPolFock (D := w.D Z) ψ θ V W A B f ↔ IsPolFock (D := w.D (setDivZ Z N h)) ψ θ V W A B f :=
  ⟨fun ⟨J, x, rest⟩ => ⟨J, ⟨x.cont, x.real, x.sq, x.symp, x.kcomm, x.defin⟩, rest⟩,
   fun ⟨J, x, rest⟩ => ⟨J, ⟨x.cont, x.real, x.sq, x.symp, x.kcomm, x.defin⟩, rest⟩⟩

@[reducible] def besDatTr {A B : TH.HSp (w.D Z)} {ι : A.V →ₗ[(w.D Z).host.E] B.V} (d : BesDat (D := w.D Z) A B ι) :
    BesDat (D := w.D (setDivZ Z N h)) A B ι := { d with }


set_option maxHeartbeats 4000000 in
def thetaTiedTr {X : ThetaX (w.D Z)} (T : ThetaTied (w.D Z) X) : ThetaTied (w.D (setDivZ Z N h)) (thTrZ w Z N h X) :=
  { T with ev_aut := fun V F => (isAutFun_tr w Z N h).1 (T.ev_aut V F) }


set_option maxHeartbeats 4000000 in
def weilTiedTr {X : ThetaX (w.D Z)} {T : ThetaTied (w.D Z) X} (Wl : WeilTied (w.D Z) X T) :
    WeilTied (w.D (setDivZ Z N h)) (thTrZ w Z N h X) (thetaTiedTr w Z N h T) :=
  { Wl with
    evS_range := fun V W hne => (Wl.evS_range V W hne).trans (Set.ext fun _ => isThetaFun_tr w Z N h)
    om_tw := { Wl.om_tw with } }


set_option maxHeartbeats 4000000 in
theorem weilTiedEq_tr {X : ThetaX (w.D Z)} {T : ThetaTied (w.D Z) X} {Wl : WeilTied (w.D Z) X T} (e : WeilCompatibleEquivariance Wl) :
    WeilCompatibleEquivariance (weilTiedTr w Z N h Wl) :=
  { e with
    evS_range := fun V W hr => (e.evS_range V W hr).trans (Set.ext fun _ => isThetaFun_tr w Z N h)
    om_tw := { e.om_tw with } }


set_option maxHeartbeats 4000000 in
def allTiedTr {X : ThetaX (w.D Z)} {A : TH.ProvA} (a : AllTied (w.D Z) X A) : AllTied (w.D (setDivZ Z N h)) (thTrZ w Z N h X) A where
  T := thetaTiedTr w Z N h a.T
  sm := ⟨a.sm.1, fun θ hθ V hV => (a.sm.2 θ hθ V hV).trans (Set.ext fun _ => isAutFunSm_tr w Z N h)⟩
  ty := { a.ty with }
  W := weilTiedTr w Z N h a.W
  unr := a.unr
  kf := { a.kf with
    kfin := ⟨a.kf.kfin.1, fun θ hθ V W h1 h2 h3 Φ => (a.kf.kfin.2 θ hθ V W h1 h2 h3 Φ).trans (isPolFock_tr w Z N h)⟩ }
  phiUp := a.phiUp
  B := { a.B with dat := fun A B ι ho p => besDatTr w Z N h (a.B.dat A B ι ho p) }
  real := { a.real with }
  prov := { a.prov with }


end

set_option maxHeartbeats 16000000 in
theorem thT_setDiv {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)}
    (n : NchT w Z Wt nch) (th : ThetaX (w.D Z))
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) :
    ThT n th →
      let moved : NchT w (setDivZ Z N h) Wt { nch with } :=
        { n with tp := { n.tp with }, tie := { n.tie with }, chrPsi := n.chrPsi }
      Nonempty (ThT moved (thTrZ w Z N h th)) := by
  intro t
  exact ⟨{ provA := t.provA
           all := allTiedTr w Z N h t.all
           weq := weilTiedEq_tr w Z N h t.weq
           chr := { t.chr with }
           same := { t.same with }
           std := t.std
           io := t.io }⟩

end GlobalTheory.Mem.Top.Bl.ThTTr
end

