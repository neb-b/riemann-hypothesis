module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicSupportedAtBadPrimePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0003
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFreeSeriesKernelServedPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerTieServed
open MvPowerSeries

section Lin
variable {p : ℕ} [Fact p.Prime] {σ σ' : Type*} [Fintype σ] [Fintype σ']

theorem hasSubst_linear {κ : Type*} [Fintype κ] (c : σ → κ → ℂ_[p]) :
    HasSubst (fun k : σ => ∑ x : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k x) * X x) :=
  hasSubst_of_constantCoeff_zero fun k => by simp

theorem linAt_comp {κ : Type*} [Fintype κ] (c₁ : σ → σ' → ℂ_[p]) (c₂ : σ' → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    linAt c₂ (linAt c₁ F) = linAt (fun k x => ∑ j, c₁ k j * c₂ j x) F := by
  unfold linAt
  rw [subst_comp_subst_apply (hasSubst_linear c₁) (hasSubst_linear c₂)]
  congr 1
  funext k
  rw [← coe_substAlgHom (hasSubst_linear c₂)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, AlgHom.commutes, substAlgHom_X, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem linAt_delta [DecidableEq σ] (F : MvPowerSeries σ ℂ_[p]) :
    linAt (fun k x : σ => if k = x then (1 : ℂ_[p]) else 0) F = F := by
  unfold linAt
  have e : (fun k : σ => ∑ x : σ, algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (if k = x then (1 : ℂ_[p]) else 0) * X x) =
      X := by
    funext k
    simp [apply_ite]
  rw [e, subst_self]
  rfl

end Lin

section Mat
variable {K : Type*} [Field K] {T J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

def blk (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J) (τ : T) : Matrix J I K :=
  if ev τ then (A τ).submatrix id e else ((A τ)⁻¹).transpose.submatrix id e

def blkInv (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J) (τ : T) : Matrix I J K :=
  if ev τ then ((A τ)⁻¹).submatrix e id else (A τ).transpose.submatrix e id

theorem blkInv_mul_blk (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J)
    (hA : ∀ τ, IsUnit (A τ).det) (τ : T) : blkInv ev A e τ * blk ev A e τ = 1 := by
  unfold blk blkInv
  split_ifs
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul _ (hA τ),
      Matrix.submatrix_one_equiv]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (hA τ), Matrix.transpose_one,
      Matrix.submatrix_one_equiv]

end Mat

section Sum
variable {K : Type*} [CommRing K] {S T J₁ J₂ I₁ I₂ : Type*} [Fintype T] [DecidableEq T] [Fintype J₁] [Fintype J₂]
  [DecidableEq S] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq J₁] [DecidableEq J₂]

def coef (t : S → T) (P : T → Matrix J₂ I₂ K) (Q : T → Matrix I₁ J₁ K) : T × J₂ × J₁ → S × I₁ × I₂ → K :=
  fun k x => if t x.1 = k.1 then P k.1 k.2.1 x.2.2 * Q k.1 x.2.1 k.2.2 else 0

def coefInv (t : S → T) (P' : T → Matrix I₂ J₂ K) (Q' : T → Matrix J₁ I₁ K) : S × I₁ × I₂ → T × J₂ × J₁ → K :=
  fun x k => if t x.1 = k.1 then P' k.1 x.2.2 k.2.1 * Q' k.1 k.2.2 x.2.1 else 0

theorem sum_coefInv_coef (t : S → T) (ht : Function.Injective t) (P : T → Matrix J₂ I₂ K) (Q : T → Matrix I₁ J₁ K)
    (P' : T → Matrix I₂ J₂ K) (Q' : T → Matrix J₁ I₁ K) (hP : ∀ τ, P' τ * P τ = 1) (hQ : ∀ τ, Q τ * Q' τ = 1)
    (x x' : S × I₁ × I₂) :
    ∑ k, coefInv t P' Q' x k * coef t P Q k x' = if x = x' then 1 else 0 := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (t x.1)]
  · unfold coef coefInv
    simp only [if_true]
    by_cases hxx : t x'.1 = t x.1
    · have h1 : x'.1 = x.1 := ht hxx
      simp only [hxx, if_true]
      have e : ∀ y : J₂ × J₁, P' (t x.1) x.2.2 y.1 * Q' (t x.1) y.2 x.2.1 * (P (t x.1) y.1 x'.2.2 * Q (t x.1) x'.2.1 y.2) =
          (P' (t x.1) x.2.2 y.1 * P (t x.1) y.1 x'.2.2) * (Q (t x.1) x'.2.1 y.2 * Q' (t x.1) y.2 x.2.1) := fun y => by ring
      rw [Finset.sum_congr rfl fun y _ => e y, Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      have e1 := congrFun (congrFun (hP (t x.1)) x.2.2) x'.2.2
      have e2 := congrFun (congrFun (hQ (t x.1)) x'.2.1) x.2.1
      rw [Matrix.mul_apply] at e1 e2
      rw [e1, e2, Matrix.one_apply, Matrix.one_apply]
      obtain ⟨a, b, c⟩ := x
      obtain ⟨a', b', c'⟩ := x'
      simp only at h1 ⊢
      subst h1
      rcases eq_or_ne b b' with rfl | hb <;> rcases eq_or_ne c c' with rfl | hc <;>
        first | (simp; done) | (simp [hb, hb.symm]; done) | (simp [hc, hc.symm]; done) | simp [hb, hb.symm, hc, hc.symm]
    · have hne : x ≠ x' := fun hx => hxx (by rw [hx])
      simp only [hxx, if_false, mul_zero, Finset.sum_const_zero, hne]
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun y _ => ?_
    unfold coefInv
    rw [if_neg (Ne.symm hτ), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end Sum

section Main

theorem isUnit_det_rhoMat {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : G.Fills (D.gat u w h)} {Lv : G.Levels Fl}
    {Ch : G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) (j : ℕ) (τ : D.what₂.Tau)
    (g : ∀ v, Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v)) (hg : ∀ v, IsUnit (g v).det) :
    IsUnit (rhoMat Kp j τ g).det := by
  unfold rhoMat
  have e := RingHom.map_det (Kp.iK.comp (((Fl.Pj j).ι ((posJ Gt u w h Fl j).symm τ).1).comp
    (RingEquiv.toRingHom (((Fl.Pj j).σ ((posJ Gt u w h Fl j).symm τ).1) ^ ((posJ Gt u w h Fl j).symm τ).2.val))))
    (g ((posJ Gt u w h Fl j).symm τ).1)
  rw [RingHom.mapMatrix_apply] at e
  have hu := (hg ((posJ Gt u w h Fl j).symm τ).1).map (Kp.iK.comp (((Fl.Pj j).ι ((posJ Gt u w h Fl j).symm τ).1).comp
    (RingEquiv.toRingHom (((Fl.Pj j).σ ((posJ Gt u w h Fl j).symm τ).1) ^ ((posJ Gt u w h Fl j).symm τ).2.val))))
  rw [e] at hu
  exact hu


open Classical in
theorem exists_th_served : ∀ {D : D7} {Dx : DivX D} (Gt : GatTies D) {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : G.Fills (D.gat u w h)} {Lv : G.Levels Fl}
    (KD : Formalism.L2.G.Cmp.KerData D c Tw u w h Lv) (E : KerEnt D Dx Tw), KD.lam = E.lam w →
    ∃ Th, ThAtServed (Formalism.L2.G.Cmp.kerAtP_of Gt { KD with Th := Th }) E := by
  intro D Dx Gt c Tw u w h Fl Lv KD E hlam
  let g : ∀ (j : ℕ) (_ : Lv.comp j × (Fl.Pj j).Tup) (v : Fin (Fl.Pj j).nV),
      Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v) :=
    fun j La v => if hL : (Fl.Pj j).IsLatTup La.2 then (hL v).choose else 1
  have hg : ∀ j La v, IsUnit (g j La v).det := by
    intro j La v
    by_cases hL : (Fl.Pj j).IsLatTup La.2
    · simp only [g, dif_pos hL]; exact (hL v).choose_spec.1
    · simp only [g, dif_neg hL, Matrix.det_one]; exact isUnit_one
  let K0 := Formalism.L2.G.Cmp.kerAtP_of Gt KD
  let ev : ℕ → D.what₂.Tau → Prop := fun j τ => Formalism.MainNotions.G.IsTypeV ((posJ Gt u w h Fl j).symm τ).2
  let Th : ∀ j, Lv.comp j × (Fl.Pj j).Tup → Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup →
      MvPowerSeries (D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w] :=
    fun j La La' => if hh : (Fl.Pj j).m + 1 = D.R.N j ∧ (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1) then
      linAt (coefInv (Formalism.BasicNotions.tauPl D)
          (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hh.2.symm))
          (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hh.1.symm)))
        (E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2))
    else 0
  refine ⟨Th, hlam, g, ?_, ?_⟩
  · intro j _ La hL v
    refine ⟨hg j La v, ?_⟩
    simp only [g, dif_pos hL]
    exact (hL v).choose_spec.2
  · intro j _ hN hN' La La' _ _
    refine ⟨fun _ => 1, fun _ => norm_one, ?_⟩
    have hTh : Th j La La' = linAt (coefInv (Formalism.BasicNotions.tauPl D)
          (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm)))
        (E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2)) := by
      simp only [Th, dif_pos (And.intro hN hN')]
    have hC : (fun (k : D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1))
              (x : (Bool × G.HH D) × Fin (D.R.N j) × Fin (D.R.N (j + 1))) =>
            if Formalism.BasicNotions.tauPl D x.1 = k.1 then
              (if Formalism.MainNotions.G.IsTypeV ((posJ Gt u w h Fl j).symm k.1).2 then
                (fun _ => (1 : ℂ_[D.what₂.places.resChar w])) k.1 * (rhoMat K0 (j + 1) k.1 (g (j + 1) La')) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat K0 j k.1 (g j La))⁻¹) (Fin.cast hN.symm x.2.1) k.2.2
              else
                (fun _ => (1 : ℂ_[D.what₂.places.resChar w])) k.1 * (((rhoMat K0 (j + 1) k.1 (g (j + 1) La'))⁻¹).transpose) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat K0 j k.1 (g j La)).transpose) (Fin.cast hN.symm x.2.1) k.2.2)
            else 0) =
        coef (Formalism.BasicNotions.tauPl D) (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm)) := by
      funext k x
      simp only [coef, blk, blkInv, ev]
      split_ifs <;> simp [Matrix.submatrix_apply, Matrix.transpose_apply]
    have hS := sum_coefInv_coef (Formalism.BasicNotions.tauPl D) (Formalism.BasicNotions.tauPl_bij D).1
      (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
      (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))
      (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
      (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))
      (blkInv_mul_blk _ _ _ fun τ => isUnit_det_rhoMat K0 (j + 1) τ _ (hg (j + 1) La'))
      (blkInv_mul_blk _ _ _ fun τ => isUnit_det_rhoMat K0 j τ _ (hg j La))
    have key : E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2) =
        linAt (coef (Formalism.BasicNotions.tauPl D) (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))) (Th j La La') := by
      rw [hTh, linAt_comp]
      simp only [hS]
      exact (linAt_delta _).symm
    rw [← hC] at key
    exact key

end Main

end GlobalTheory.KerTieServed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.OnePrime

section Local

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem exists_bound {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    ∃ k : ℕ, ∀ r s, Valued.v (A r s) ≤ WithZero.exp (k : ℤ) := by
  first
  | exact @_root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp
  | exact _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp
  | (apply _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp ..)

theorem mul_bound {m : ℕ} {A C : Matrix (Fin m) (Fin m) K} {a c : WithZero (Multiplicative ℤ)}
    (hA : ∀ r s, Valued.v (A r s) ≤ a) (hC : ∀ r s, Valued.v (C r s) ≤ c) (r s : Fin m) :
    Valued.v ((A * C) r s) ≤ a * c := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hA r j) (hC j s)

end Local

theorem exists_root_rat (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (m n N : ℕ) (hn : 0 < n)
    (q : P.adicCompletion E) (hq : Valued.v q = WithZero.exp (-1 : ℤ)) (G₁ G₂ : GL (Fin m) (P.adicCompletion E)) :
    ∃ (M : GL (Fin m) (P.adicCompletion E)) (γ : GL (Fin m) E),
      (∀ r s, Valued.v (M.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      (∀ r s, Valued.v ((M ^ n).1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      G₁ * M ^ n * G₂ = Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ := by
  haveI : CharZero (P.adicCompletion E) := algebraRat.charZero _
  have hc : Valued.v (q ^ (N + 1)) = WithZero.exp (-((N : ℤ) + 1)) := by
    rw [map_pow, hq, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hn1 : Valued.v (n : P.adicCompletion E) ≤ 1 := by
    clear hn
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact Valuation.map_add_le _ ih (by simp)
  have hcN : Valued.v (q ^ (N + 1)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [hc]
    exact WithZero.exp_le_exp.2 (by omega)
  have hε : Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1)) ≠ 0 := by
    rw [map_mul, hc]
    refine mul_ne_zero ?_ WithZero.exp_ne_zero
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨k₁, hk₁⟩ := exists_bound G₂.1
  obtain ⟨k₂, hk₂⟩ := exists_bound (G₂⁻¹).1
  set e := WithZero.log (Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1))) with he
  obtain ⟨γ, hγ⟩ := GlobalTheory.DenseGL.dense_two_sided E P m (k₁ + k₂ + (-e).toNat) (G₁ * G₂)
  let γ' : GL (Fin m) (P.adicCompletion E) := Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ
  have hγ' : γ'.1 = γ.1.map (algebraMap E (P.adicCompletion E)) := rfl
  let B₀ : GL (Fin m) (P.adicCompletion E) := G₁⁻¹ * γ' * G₂⁻¹
  have hB : B₀.1 - 1 = G₂.1 * (((G₁ * G₂)⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) * (G₂⁻¹).1 := by
    rw [← hγ', mul_sub, _root_.sub_mul, mul_one, Units.mul_inv, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
    congr 2
    simp only [B₀]
    group
  have hB2 : ∀ r s, Valued.v ((B₀.1 - 1) r s) ≤ Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1)) := fun r s => by
    rw [hB]
    refine (mul_bound (mul_bound hk₁ fun r s => (hγ r s).1) hk₂ r s).trans ?_
    rw [← WithZero.exp_log hε, ← he, ← WithZero.exp_add, ← WithZero.exp_add]
    refine WithZero.exp_le_exp.2 ?_
    push_cast
    omega
  obtain ⟨M, hM1, hM2⟩ := GlobalTheory.MatNthRoot.exists_nthRoot E P m n (q ^ (N + 1)) B₀.1 hn
    (by rw [hc, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)) hB2
  have hu : IsUnit M := (isUnit_pow_iff hn.ne').1 (hM2 ▸ B₀.isUnit)
  obtain ⟨M, rfl⟩ := hu
  have hM3 : M ^ n = B₀ := Units.ext (by rw [Units.val_pow_eq_pow_val, hM2])
  refine ⟨M, γ, fun r s => (hM1 r s).trans ?_, fun r s => ?_, ?_⟩
  · rw [map_mul]
    exact (mul_le_of_le_one_left' hn1).trans hcN
  · rw [hM3]
    refine (hB2 r s).trans ?_
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_left' (pow_le_one' hn1 2)).trans hcN
  · rw [hM3]
    show _ = γ'
    simp only [B₀]
    group


set_option maxHeartbeats 2000000 in
theorem exists_level_elt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), ChiFin I l Z S → ∀ (P : SBof I a), P.1 ∈ I.Q a → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ (N : ℕ) (g₁ g₂ : GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z.1 = 1) ∧ GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z.1 ∧ ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g₁ * (show GA B (B.R.N i) from z.1) * g₂ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s) := by
  intro B X I hI hPin l Z a T i hi bad S hS P hP v hv N g₁ g₂
  obtain ⟨n, hn, hchi⟩ := hS
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep I hI hPin l Z a T i hi bad S P v hv
  have hd := fun N z => GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a ((I.rec7 l Z).R.N i) N P z
  obtain ⟨hs, hq, -⟩ := hd 0 1
  let φ : AfE B.host.F B.host.E →+* P.1.adicCompletion B.fields.E := adAt B.host.F P.1
  obtain ⟨M, γ, hM1, hM2, hM3⟩ := exists_root_rat B.fields.E P.1 (B.R.N i) n (N + N₀) hn _ hq
    (Matrix.GeneralLinearGroup.map φ g₁) (Matrix.GeneralLinearGroup.map φ g₂)
  obtain ⟨w, hwU, hwv, hwP⟩ := GlobalTheory.Mem.Col2.AdLift.exists_lift I hI hPin l Z a i hi P v hv M
  have hw : w ∈ S.U := hN₀ w hwU hwv (((hd N₀ w).2.2).2 fun r s => by
    rw [hwP]
    exact (hM1 r s).trans (WithZero.exp_le_exp.2 (by omega)))
  let w' : GA B (B.R.N i) := w
  have hw' : Matrix.GeneralLinearGroup.map φ w' = M := Units.ext (Matrix.ext hwP)
  have hz : Matrix.GeneralLinearGroup.map φ (w' ^ n) = M ^ n := by rw [map_pow, hw']
  have hz' : ∀ r s, φ ((w' ^ n).1 r s) = (M ^ n).1 r s := fun r s =>
    congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) hz
  have hbad : v ∉ badG (I.rec7 l Z) := by
    have key : ∀ j : Fin 2, (((B.primes X).g j : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal := fun j =>
      GlobalTheory.Proof.NarrowJetMoments.notMem_of_mem_QE hI.sel_ok hP ((base_fields_primes_ok B X).2.1.g_prime j) (hI.g_mem j)
    rw [hs] at hv
    have key2 : ∀ j : Fin 2, (((B.primes X).g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal := fun j h => by
      rw [hv, Ideal.mem_comap, map_natCast] at h
      exact key j h
    rintro (h | h)
    · exact key2 0 h
    · exact key2 1 h
  refine ⟨⟨w, hw⟩ ^ n, ?_, fun v' hv' => ?_, ((hd N _).2.2).2 fun r s => ?_, γ, fun r s => ?_⟩
  · rw [map_pow]
    exact hchi ⟨w, hw⟩ fun v' hv' => hwv v' fun e => hbad (e ▸ hv')
  · show bc (prV (E := (I.rec7 l Z).host.E) v') (w ^ n) = 1
    calc
      bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v') (w ^ n) =
          (bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v') w) ^ n := map_pow _ _ _
      _ = 1 := (congrArg (fun x => x ^ n) (hwv v' hv')).trans (one_pow n)
  · have e := hz' r s
    have h2 := hM2 r s
    rw [← e] at h2
    exact h2.trans (WithZero.exp_le_exp.2 (by omega))
  · have e : Matrix.GeneralLinearGroup.map φ (g₁ * w' ^ n * g₂) =
        Matrix.GeneralLinearGroup.map φ g₁ * M ^ n * Matrix.GeneralLinearGroup.map φ g₂ := by
      rw [map_mul, map_mul, hz]
    exact congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) (e.trans hM3)

end GlobalTheory.Mem.Col2.AdT.OnePrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalCoefficientFieldEmbeddingKernelPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerIK

open Cardinal

theorem kf_hom_of_isRec {sc : Scale} {D : D7} {Gt : GatTies D} {c : LatCmp D} {H : Formalism.L2.Herm.Herm0 D}
    {F : ∀ u, Formalism.L2.Forms.Forms0 D u} (h : IsRecG sc D Gt c H F) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) [Fact (D.what₂.places.resChar v).Prime] :
    Nonempty ((D.gat u v hg).Kf →+* ℂ_[D.what₂.places.resChar v]) := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, eq⟩ := h
  cases eq
  exact ⟨iK u v hg⟩

theorem mk_LL_le (D : D7) : #D.what₂.LL ≤ ℵ₀ := by
  have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL
  rwa [Cardinal.mkRat, max_self] at this

theorem exists_iK : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ iK : ((w.D Z).gat u v hg).Kf →+* ℂ_[(w.D Z).what₂.places.resChar v],
        ∀ (x : (w.D Z).what₂.LL) (hx : (w.D Z).what₂.embLL x ∈ algebraicClosure ℚ ℂ),
          iK (t.cmp.embW u v hg x) = E.lam v ⟨(w.D Z).what₂.embLL x, hx⟩ := by
  intro K B f T w _ _ _ Z t Wt nch _ Y _ _ O _ _ E _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨i0⟩ := kf_hom_of_isRec t.isRec u v hg
  have hC : ℵ₀ < #ℂ_[(w.D Z).what₂.places.resChar v] :=
    Cardinal.aleph0_lt_continuum.trans_le (continuum_le_cardinal_of_nontriviallyNormedField _)
  obtain ⟨σ, hσ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extEmb_equiv_comp (i0.comp (t.cmp.embW u v hg)) (E.iL v)
    (mk_LL_le (w.D Z)) hC rfl
  refine ⟨σ.toRingHom.comp i0, fun x hx => ?_⟩
  have h1 := hσ x
  have h2 := E.iL_lam v x
  simp only [RingHom.comp_apply] at h1
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [h1, h2, lamV, dite_eq_left hx]

end GlobalTheory.KerIK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincLocStep
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.Opn

theorem exists_princ_loc_step : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n T f : ℕ} {J : Matrix (Fin n) (Fin n) E} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)), J = 1 → ∃ M : ℕ, 0 < M ∧ ∀ y ∈ UPts σ J (v.adicCompletion F), (∀ a b, ∃ c ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring, ((y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) a b = (M : E ⊗[F] v.adicCompletion F) * c) → y ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n T f J bad S v hJ
  subst hJ
  obtain ⟨M, hM, hMU⟩ := GlobalTheory.Mem.Col2.AdT.Opn.exists_princ σ S.U S.U_open
  refine ⟨M, Nat.pos_of_ne_zero hM, fun y hy hc => ?_⟩
  choose C hC hyC using hc
  have hz := Formalism.UG.P.afsplitU_mem v σ 1 y 1 hy (one_mem _)
  have hzU : Formalism.UG.P.afsplitU v y 1 ∈ S.U := by
    refine hMU _ hz fun a b => ?_
    have hyab : (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b + M • C a b := by
      rw [nsmul_eq_mul, ← hyC a b, Matrix.sub_apply, add_sub_cancel]
    have e : (((Formalism.UG.P.afsplitU v y 1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b =
        (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * Formalism.UG.P.afsplitIE v (C a b) := by
      rw [Matrix.sub_apply, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_apply, Units.val_one, hyab, map_add (f := _), map_nsmul,
        nsmul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.one_apply_eq, Formalism.UG.P.afsplitEps]
        ring
      · simp [Matrix.one_apply_ne hab]
    rw [e, ← mul_assoc, ← map_natCast (Formalism.L2.Col.iA F E), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one, one_mul]
    exact Formalism.UG.P.afsplit_IE_int v _ (hC a b)
  have h := ((S.U_eq _).1 hzU).2 v
  rwa [Formalism.UG.P.afsplit_right1] at h

end GlobalTheory.Mem.Col2.AdT.Opn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTopStepLevelCongruentBlockSumOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topStep_level_congruent_blockSum_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g g' z, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P g z ∧ LiftsInv I κ P g' ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) g g' := by
  first | exact @GlobalTheory.Mem.Col2.AdT.exists_topLev_liftsInv | exact GlobalTheory.Mem.Col2.AdT.exists_topLev_liftsInv | (intros; apply GlobalTheory.Mem.Col2.AdT.exists_topLev_liftsInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicSupportedAtBadPrimePlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelic_supported_at_bad_prime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ A : GL (Fin ((I.rec7 l Z).R.N i)) (P.1.adicCompletion B.fields.E), ∃ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) ∧ ∀ r s, adAt B.host.F P.1 (z.1 r s) = A.1 r s := by
  first | exact @GlobalTheory.Mem.Col2.AdLift.exists_lift | exact GlobalTheory.Mem.Col2.AdLift.exists_lift | (intros; apply GlobalTheory.Mem.Col2.AdLift.exists_lift <;> assumption)
end

