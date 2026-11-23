module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0416
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0437
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulPow
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MatNthRoot

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}

def Bnd (r : WithZero (Multiplicative ℤ)) (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) : Prop :=
  ∀ i j, Valued.v (X i j) ≤ r

theorem v_natCast_le_one (m : ℕ) : Valued.v ((m : P.adicCompletion E)) ≤ 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

variable {r s : WithZero (Multiplicative ℤ)} {X Y : Matrix (Fin N) (Fin N) (P.adicCompletion E)}

theorem bnd_add (hX : Bnd r X) (hY : Bnd r Y) : Bnd r (X + Y) := fun i j =>
  (Valuation.map_add _ _ _).trans (max_le (hX i j) (hY i j))

theorem bnd_neg (hX : Bnd r X) : Bnd r (-X) := fun i j => by
  rw [Matrix.neg_apply, Valuation.map_neg]; exact hX i j

theorem bnd_sub (hX : Bnd r X) (hY : Bnd r Y) : Bnd r (X - Y) := by
  rw [sub_eq_add_neg]; exact bnd_add hX (bnd_neg hY)

theorem bnd_smul (a : P.adicCompletion E) (hX : Bnd r X) : Bnd (Valued.v a * r) (a • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]; exact mul_le_mul' le_rfl (hX i j)

theorem bnd_mul (hX : Bnd r X) (hY : Bnd s Y) : Bnd (r * s) (X * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by rw [Valuation.map_mul]; exact mul_le_mul' (hX i k) (hY k j)

theorem bnd_mono (h : r ≤ s) (hX : Bnd r X) : Bnd s X := fun i j => (hX i j).trans h

theorem bnd_zero : Bnd r (0 : Matrix (Fin N) (Fin N) (P.adicCompletion E)) := fun i j => by simp

theorem bnd_one : Bnd 1 (1 : Matrix (Fin N) (Fin N) (P.adicCompletion E)) := fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem bnd_sum {ι : Type} (t : Finset ι) (f : ι → Matrix (Fin N) (Fin N) (P.adicCompletion E))
    (h : ∀ k ∈ t, Bnd r (f k)) : Bnd r (∑ k ∈ t, f k) := fun i j => by
  rw [Matrix.sum_apply]; exact Valuation.map_sum_le _ fun k hk => h k hk i j

theorem bnd_pow (hX : Bnd 1 X) : ∀ k : ℕ, Bnd 1 (X ^ k)
  | 0 => by rw [pow_zero]; exact bnd_one
  | k + 1 => by rw [pow_succ]; simpa only [one_mul] using bnd_mul (bnd_pow hX k) hX

theorem bnd_pow_sub (hX : Bnd 1 X) (hY : Bnd 1 Y) (hXY : Bnd r (X - Y)) :
    ∀ k : ℕ, Bnd r (X ^ k - Y ^ k)
  | 0 => by rw [pow_zero, pow_zero, sub_self]; exact bnd_zero
  | k + 1 => by
    have e : X ^ (k + 1) - Y ^ (k + 1) = X ^ k * (X - Y) + (X ^ k - Y ^ k) * Y := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [e]
    exact bnd_add (by simpa only [one_mul] using bnd_mul (bnd_pow hX k) hXY)
      (by simpa only [mul_one] using bnd_mul (bnd_pow_sub hX hY hXY k) hY)

noncomputable def tail (n : ℕ) (c : P.adicCompletion E) (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) :
    Matrix (Fin N) (Fin N) (P.adicCompletion E) :=
  ∑ k ∈ Finset.range (n - 1), ((n.choose (k + 2) : P.adicCompletion E) * ((n : P.adicCompletion E) * c) ^ k) • X ^ (k + 2)

theorem v_coef_le_one (n k : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) :
    Valued.v ((n.choose (k + 2) : P.adicCompletion E) * ((n : P.adicCompletion E) * c) ^ k) ≤ 1 := by
  rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_mul]
  exact mul_le_one' (v_natCast_le_one _) (pow_le_one' (mul_le_one' (v_natCast_le_one _) hc) _)

theorem bnd_tail (n : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) (hX : Bnd 1 X) :
    Bnd 1 (tail n c X) :=
  bnd_sum _ _ fun k _ => bnd_mono (by simpa only [mul_one] using v_coef_le_one n k hc)
    (bnd_smul _ (bnd_pow hX _))

theorem bnd_tail_sub (n : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) (hX : Bnd 1 X) (hY : Bnd 1 Y)
    (hXY : Bnd r (X - Y)) : Bnd r (tail n c X - tail n c Y) := by
  unfold tail
  rw [← Finset.sum_sub_distrib]
  refine bnd_sum _ _ fun k _ => ?_
  rw [← smul_sub]
  exact bnd_mono (by simpa only [one_mul] using mul_le_mul' (v_coef_le_one n k hc) (le_refl r))
    (bnd_smul _ (bnd_pow_sub hX hY hXY _))

theorem one_add_smul_pow (n : ℕ) (hn : 0 < n) (c : P.adicCompletion E)
    (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) :
    (1 + ((n : P.adicCompletion E) * c) • X) ^ n =
      1 + ((n : P.adicCompletion E) ^ 2 * c) • (X + c • tail n c X) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [add_comm (1 : Matrix _ _ _), (Commute.one_right _).add_pow]
  simp only [one_pow, mul_one]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [tail, Nat.add_sub_cancel, smul_add, Finset.smul_sum, smul_smul, smul_pow]
  have hc : ∀ (j : ℕ) (Z : Matrix (Fin N) (Fin N) (P.adicCompletion E)),
      Z * ((j : ℕ) : Matrix (Fin N) (Fin N) (P.adicCompletion E)) = (j : P.adicCompletion E) • Z := by
    intro j Z
    rw [← Nat.cast_comm, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  simp only [hc, smul_smul]
  have hs : ∀ x ∈ Finset.range m,
      (((m + 1).choose (x + 1 + 1) : P.adicCompletion E) * (((m + 1 : ℕ) : P.adicCompletion E) * c) ^ (x + 1 + 1)) •
        X ^ (x + 1 + 1) =
      (((m + 1 : ℕ) : P.adicCompletion E) ^ 2 * c * (c * (((m + 1).choose (x + 2) : P.adicCompletion E) *
        (((m + 1 : ℕ) : P.adicCompletion E) * c) ^ x))) • X ^ (x + 2) := by
    intro x _
    rw [show x + 1 + 1 = x + 2 by omega]
    congr 1
    ring
  rw [Finset.sum_congr rfl hs]
  simp only [zero_add, Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, Nat.cast_one,
    one_mul, one_smul]
  have e : ((m + 1 : ℕ) : P.adicCompletion E) * (((m + 1 : ℕ) : P.adicCompletion E) * c) =
      ((m + 1 : ℕ) : P.adicCompletion E) ^ 2 * c := by ring
  rw [e]
  abel

end GlobalTheory.MatNthRoot

namespace GlobalTheory.MatNthRoot

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}

theorem exists_nthRoot : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (N n : ℕ)
    (c : P.adicCompletion E) (A : Matrix (Fin N) (Fin N) (P.adicCompletion E)), 0 < n → Valued.v c < 1 →
    (∀ i j, Valued.v ((A - 1) i j) ≤ Valued.v ((n : P.adicCompletion E) ^ 2 * c)) →
    ∃ M : Matrix (Fin N) (Fin N) (P.adicCompletion E),
      (∀ i j, Valued.v ((M - 1) i j) ≤ Valued.v ((n : P.adicCompletion E) * c)) ∧ M ^ n = A := by
  intro E _ _ P N n c A hn hc hA
  have hc1 : Valued.v c ≤ 1 := hc.le
  rcases eq_or_ne c 0 with rfl | hc0
  · refine ⟨1, fun i j => by simp, ?_⟩
    rw [one_pow]
    have hA1 : A - 1 = 0 := Matrix.ext fun i j => by
      have h := hA i j
      rwa [mul_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at h
    exact (sub_eq_zero.1 hA1).symm
  have hn0 : (n : P.adicCompletion E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set s : P.adicCompletion E := (n : P.adicCompletion E) ^ 2 * c with hs
  have hs0 : s ≠ 0 := mul_ne_zero (pow_ne_zero _ hn0) hc0
  set Y : Matrix (Fin N) (Fin N) (P.adicCompletion E) := s⁻¹ • (A - 1) with hYdef
  have hY : Bnd 1 Y := fun i j => by
    rw [hYdef, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
    calc Valued.v s⁻¹ * Valued.v ((A - 1) i j) ≤ Valued.v s⁻¹ * Valued.v s := mul_le_mul' le_rfl (hA i j)
      _ = 1 := by rw [← Valuation.map_mul, inv_mul_cancel₀ hs0, Valuation.map_one]
  let f : Matrix (Fin N) (Fin N) (P.adicCompletion E) → Matrix (Fin N) (Fin N) (P.adicCompletion E) :=
    fun X => Y - c • tail n c X
  have hf1 : ∀ X, Bnd 1 X → Bnd 1 (f X) := fun X hX =>
    bnd_sub hY (bnd_mono (by simpa only [mul_one] using hc1) (bnd_smul c (bnd_tail n hc1 hX)))
  have hfl : ∀ X Z r, Bnd 1 X → Bnd 1 Z → Bnd r (X - Z) → Bnd (Valued.v c * r) (f X - f Z) := by
    intro X Z r hX hZ hXZ
    have e : f X - f Z = -(c • (tail n c X - tail n c Z)) := by
      simp only [f, smul_sub]; abel
    rw [e]
    exact bnd_neg (bnd_smul c (bnd_tail_sub n hc1 hX hZ hXZ))
  have hb : ∀ k : ℕ, Bnd 1 (f^[k] 0) := by
    intro k
    induction k with
    | zero => exact bnd_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact hf1 _ ih
  have hd : ∀ k : ℕ, Bnd (Valued.v c ^ k) (f^[k + 1] 0 - f^[k] 0) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact bnd_sub (hb 1) (hb 0)
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := hfl _ _ _ (hb (k + 1)) (hb k) ih
      rwa [← Function.iterate_succ_apply' f k 0, ← pow_succ'] at this
  have hcau : ∀ i j, CauchySeq fun k => (f^[k] 0) i j := by
    intro i j
    refine cauchySeq_of_le_geometric ‖c‖ 1 (Valued.toNormedField.norm_lt_one_iff.2 hc) fun k => ?_
    rw [dist_eq_norm', one_mul, ← norm_pow]
    refine Valued.toNormedField.norm_le_iff.2 ?_
    rw [Valuation.map_pow]
    have := hd k i j
    rwa [Matrix.sub_apply] at this
  choose L hL using fun i j => cauchySeq_tendsto_of_complete (hcau i j)
  set L' : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Matrix.of L with hL'
  have hT : Filter.Tendsto (fun k => f^[k] 0) Filter.atTop (nhds L') :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hL i j
  have hfc : Continuous f := by
    simp only [f, tail]
    fun_prop
  have hfix : f L' = L' := by
    have h1 : Filter.Tendsto (fun k => f^[k + 1] 0) Filter.atTop (nhds L') :=
      hT.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun k => f^[k + 1] 0) Filter.atTop (nhds (f L')) := by
      simp only [Function.iterate_succ_apply']
      exact (hfc.tendsto L').comp hT
    exact tendsto_nhds_unique h2 h1
  have hLb : Bnd 1 L' := by
    intro i j
    have hm := (Valued.isClosed_valuationSubring (P.adicCompletion E)).mem_of_tendsto (hL i j)
      (Filter.Eventually.of_forall fun k => (Valuation.mem_valuationSubring_iff _ _).2 (hb k i j))
    exact (Valuation.mem_valuationSubring_iff _ _).1 hm
  refine ⟨1 + ((n : P.adicCompletion E) * c) • L', fun i j => ?_, ?_⟩
  · rw [add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
    simpa only [mul_one] using mul_le_mul' (le_refl (Valued.v ((n : P.adicCompletion E) * c))) (hLb i j)
  · rw [one_add_smul_pow n hn c L']
    have e : L' + c • tail n c L' = Y := by
      nth_rewrite 1 [← hfix]
      simp only [f]
      abel
    rw [e, hYdef, smul_smul, ← hs, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]

end GlobalTheory.MatNthRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QpIsQpSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.QpIsOf

theorem qpIs_qpSet : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), ColPin w → ∀ (Z : w.Lt) {nch : NChoice (w.D Z)}
    (tp : Formalism.L2.Host.TupTied (w.D Z) (TC.cf w.I w.l Z) nch), tp.xi = w.I.xi → GlobalTheory.Mem.HD.TupPins tp →
    TC.QpIs w.I (GlobalTheory.Mem.HD.ReQ.qpSet tp) := by
  intro B f T w _ Z nch tp hxi _ a p
  classical
  have hr := w.ok.xi_reads a
  have hsel : Formalism.L2.Col.IsSel B.fields w.I.sel := w.ok.sel_ok
  have hf := GlobalTheory.OpenChrRam.qprime_finite B.fields.F B.fields.E B.fields.K ((w.I.tup a : Formalism.L2.DIV.Chr _ _ _))
    (w.I.tup a).2.1.1.1.1.2
  have hpm : ∀ (v : HeightOneSpectrum (𝓞 B.fields.F)) (P : HeightOneSpectrum (𝓞 B.fields.E)),
      Ideal.under (𝓞 B.fields.F) P.asIdeal = v.asIdeal → ((p : 𝓞 B.fields.E) ∈ P.asIdeal ↔ (p : 𝓞 B.fields.F) ∈ v.asIdeal) := by
    intro v P h
    rw [← h, Ideal.under, Ideal.mem_comap, map_natCast]
  have hx : ∀ P, (tp.xi a).UnrAt P ↔ (w.I.xi a).UnrAt P := fun P => by rw [congrFun hxi a]; exact Iff.rfl
  refine (GlobalTheory.Mem.HD.ReQ.mem_qpSet tp a p).trans ?_
  refine Iff.trans (and_congr_right fun _ => exists_congr fun P => and_congr_right fun _ => not_congr (hx P)) ?_
  show (p.Prime ∧ ∃ P, (p : 𝓞 B.fields.E) ∈ P.asIdeal ∧ ¬ (w.I.xi a).UnrAt P) ↔
    p.Prime ∧ ∃ P ∈ Formalism.L2.Col.QE w.I.sel (w.I.tup a : Formalism.L2.DIV.Chr _ _ _), (p : 𝓞 B.fields.E) ∈ P.asIdeal
  rw [Formalism.L2.Col.QE, dite_eq_left hf]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨P, hp, hP⟩
    refine ⟨w.I.sel (P.under (𝓞 B.fields.F)),
      Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ((GlobalTheory.Mem.ReadTwist.mem_qprime_iff hr _).2 ⟨P, rfl, hP⟩)), ?_⟩
    rw [hpm _ _ (hsel _), ← hpm _ P rfl]
    exact hp
  · rintro ⟨P, hP, hp⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨P', hP', hr'⟩ := (GlobalTheory.Mem.ReadTwist.mem_qprime_iff hr v).1 (hf.mem_toFinset.1 hv)
    refine ⟨P', ?_, hr'⟩
    rw [hpm v P' (by rw [← hP']; rfl), ← hpm v _ (hsel v)]
    exact hp

end GlobalTheory.Mem.Top.Bl.QpIsOf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeLatticeEqCompanionOfAdelicRep
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (h : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
      ((y⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Λ := by
  apply le_antisymm
  · rw [Formalism.L2.PairingIndexBounds.F.latAd, Submodule.span_le]
    intro x hx
    exact Formalism.L2.GlobalTheoryTheory.Br.latLocGlob_main (F := F) Λ hfin x ((h _).2 hx)
  · intro x hx
    exact Submodule.subset_span ((h _).1 (Submodule.subset_span ⟨x, hx, rfl⟩))

theorem GlobalTheory.Mem.Col2.AdT.mvL_one {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.MainNotions.G.KAat.mvL (1 : GL (Fin N) E) Λ = Λ := by
  ext x
  simp only [Formalism.MainNotions.G.KAat.mvL, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Formalism.MainNotions.G.KAat.toLE_apply, Units.val_one, Matrix.one_mulVec, exists_eq_right]

theorem GlobalTheory.Mem.Col2.AdT.sup_dual_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : Deco E n ST SG) (hd : d.Ok) (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal) (hcop : IsCoprime π (cO E π)) :
    d.L ⊔ Ideal.span {cO E π} • Formalism.HermitianLatticesTheory.dual (hStd E n) d.L = d.N := by
  ext x
  rw [GlobalTheory.Mem.Col2.MemLat.mem_N_iff d hd π hmem hcop, Submodule.mem_sup, Submodule.ideal_span_singleton_smul]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact ⟨y, hy, b, hb, rfl⟩
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨y, hy, _, Submodule.smul_mem_pointwise_smul _ _ _ hb, rfl⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ c : (I.stp u a i).Cl, ((I.stp u a i).rep c).1.1.deco.1.N = GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) ((K (chOf c)).y ⟨c, rfl⟩).1 (K (chOf c)).lev.Lb := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K k hR c
  have hsp := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hG := hsp.1
  have hL := (hsp.2.2 u a).1 c
  have hf := (l.lat u a i c).fg
  rw [← hL] at hf
  have hA := (GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS _ _ _ (Module.Finite.iff_fg.2 hf)
      ((K (chOf c)).y_lat ⟨c, rfl⟩)).trans hL
  unfold GlobalTheory.TwU.latCo
  rw [hA, hG]
  unfold Formalism.L2.PairingIndexBounds.F.compan
  rw [GlobalTheory.Mem.Col2.AdT.mvL_one]
  have key := GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual (((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E))
    (fun x => rfl) ((I.stp u a i).rep c).1.1.deco.1.L
  unfold dualL at key
  erw [key]
  have hsep := sepElt_of_ok l.pr u
  have hmem : ∀ P : (B.primes X).vT u, (B.primes X).piT u ∈ P.1.asIdeal := fun P => by
    have := hsep.conj P
    rwa [cO_cO] at this
  exact (GlobalTheory.Mem.Col2.AdT.sup_dual_eq_N ((I.stp u a i).rep c).1.1.deco.1 ((I.stp u a i).rep c).1.1.deco.2 _ hmem (l.pr.piT_cop u)).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceIdempotentCmEmbeddingCompat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

noncomputable def iw0 {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (G : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) (q : Fin (D.gat u v hg).P.nV) :
    D.host.E →+* (D.gat u v hg).P.Qq q :=
  ((G u v hg).eQ q _ rfl).symm.toRingHom.comp
    (((RingHom.fst _ _).comp ((G u v hg).spl _ ((G u v hg).pl q).2).toRingHom).comp
      (Formalism.UG.inclE (F := D.host.F) ((((G u v hg).pl q).1).adicCompletion D.host.F)))

theorem splitPlaceIdempotent_cmEmbedding_compat {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (G : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) (q : Fin (D.gat u v hg).P.nV) (x : D.host.E) :
    (G u v hg).eQ q _ rfl (iw0 G u v hg q x) =
      ((G u v hg).spl _ ((G u v hg).pl q).2
        (Formalism.UG.inclE (F := D.host.F) ((((G u v hg).pl q).1).adicCompletion D.host.F) x)).1 := by
  simp [iw0]

end GlobalTheory.Mem.Top.KerOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPointMatrixAndInverseIntegralAtEveryPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem ptOf_std_entries_intAtA : ∀ {B : Base} (n : ℕ) (g : GA B n) (p : DecoF B.fields.E n ∅ ∅ ∅), PtOf g p → p.deco.1.N = stdLat B.fields.E n → ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin n), IntAtA (F := B.host.F) P ((g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) ∧ IntAtA (F := B.host.F) P (((g⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
  intro B n g p hp hN P r s
  have hlat := hp.lat
  rw [hN] at hlat
  have hint : ∀ x : Fin n → AfE B.host.F B.host.E, x ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) ↔ ∀ i, x i ∈ Formalism.L2.Herm.intAf B.host.F B.host.E := by
    intro x
    exact mem_latS_std x
  have hone : ∀ a : AfE B.host.F B.host.E, a ∈ Formalism.L2.Herm.intAf B.host.F B.host.E → IntAtA (F := B.host.F) P a := by
    intro a ha
    refine ⟨1, ?_, ?_⟩
    · exact P.asIdeal.ne_top_iff_one.mp P.isPrime.ne_top
    · simpa using ha
  have he : ∀ j : Fin n, (Pi.single j 1 : Fin n → AfE B.host.F B.host.E) ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) := by
    intro j
    rw [hint]
    intro i
    by_cases h : i = j
    · subst h; simp [one_mem]
    · simp [Pi.single_apply, h, zero_mem]
  constructor
  · apply hone
    have hx : (g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) *ᵥ Pi.single s 1 ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) := by
      rw [hlat]
      rw [Matrix.mulVec_mulVec]
      have h1 : ((g⁻¹ : GL (Fin n) (AfE B.host.F B.host.E)) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) * (g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [h1, Matrix.one_mulVec]
      exact he s
    have := (hint _).1 hx r
    simpa [Matrix.mulVec_single] using this
  · apply hone
    have hx := (hlat (Pi.single s 1)).1 (he s)
    have := (hint _).1 hx r
    simpa [Matrix.mulVec_single] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleLayerCompatibilitiesOfXPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleLayerCompatibilities_of_X_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) (Lv : SymmetricTwistedLevelData W), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → I.StdW l Z l0 W → I.StdLv l Z l0 Lv → (∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m), ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) → ∃ (Pt : TwPTiedS Lv) (E : TwPEvzS Pt), TwPAtGS Pt ∧ I.StdP l Z l0 Pt E := by
  first | exact @GlobalTheory.Mem.Col2.TC.tupleLayer_compatibility | exact GlobalTheory.Mem.Col2.TC.tupleLayer_compatibility | (intros; apply GlobalTheory.Mem.Col2.TC.tupleLayer_compatibility <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFiniteVectorFixedPrincipalLevelCoeffSpace
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.Level

variable {D : D7}

theorem isLift_one_V {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    Lev.IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) 1 1 := by
  have h : (1 : GA D (Vc D i)) ∈ Lev.levG (Vc D i) (L.βV i) (L.datVt i t) := one_mem _
  exact ⟨h.1, h.2.1, Subgroup.mem_bot.1 h.2.2⟩

theorem levChi_flag_one {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.levChi V β (Lev.flagL L) 1 = 1 := by
  unfold Lev.levChi
  rw [(Lev.finE V).map_one]
  exact congrArg Units.val (Formalism.L2.DIV.levChar D.sp.cm V.gram β (Lev.flagL L)).map_one

theorem om_level_vP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → R.thP_vP → (∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)) → ∀ i t, ∀ k ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv), R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω hv _ i t k hk
  have h := _root_.GlobalTheory.VecInv.omega_lifts_vP R hL (hv i t).1.2.inf hω hv i t 1 1 k (isLift_one_V R.toLevCh i t)
    ⟨hk.1, hk.2.1, Subgroup.mem_bot.1 hk.2.2⟩
  rw [h, levChi_flag_one, inv_one, one_smul]

end GlobalTheory.DefLift.Level
end

