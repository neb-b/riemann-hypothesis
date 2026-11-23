module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0195
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorsInvertibleBasisOverOE
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 4000000 in
theorem GlobalTheory.LimVec.invertible_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)), (∀ n, ∃ R' : Matrix (Fin (d' n)) (Fin d) (WCb l), (∀ i j, R' i j ∈ bk.OE) ∧ ∀ i j, (l : WCb l) ^ n ∣ (R n * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ n i j, R n i j ∈ bk.OE) → ∃ V V' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, V i j ∈ bk.OE) ∧ (∀ i j, V' i j ∈ bk.OE) ∧ V * V' = 1 ∧ ∀ j k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ ((fun i => V i j) - R k *ᵥ fun a => bk.evW (s' a)) i := by
  intro l _ K bk d d' R h1 h2 h3
  have lnu : ¬ IsUnit ((l : ℕ) : WCb l) := by
    intro h
    obtain ⟨u, hu⟩ := h
    have h1 := congrArg (fun x : WCb l => x.coeff 0) u.mul_inv
    simp only [WittVector.mul_coeff_zero, WittVector.one_coeff_zero] at h1
    rw [hu, WittVector.coeff_p_zero, zero_mul] at h1
    exact zero_ne_one h1
  have evW_mem : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨hOEsat, ⟨wX, -, hwX⟩, -, hOEdec, -⟩ := _root_.GlobalTheory.OEDvr.main l K bk
  obtain ⟨-, hOEcl, -⟩ := _root_.GlobalTheory.OEStable.main l K bk
  have cU : IsUnit (bk.evW X) := ⟨⟨_, wX, hwX, by rw [mul_comm]; exact hwX⟩, rfl⟩
  set π := Ideal.Quotient.mk (Ideal.span {((l : ℕ) : WCb l)}) with hπ
  have hdvd : ∀ x : WCb l, ((l : ℕ) : WCb l) ∣ x ↔ π x = 0 := fun x => by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have πl : π ((l : ℕ) : WCb l) = 0 := (hdvd _).1 dvd_rfl
  have hdvd' : ∀ x y : WCb l, ((l : ℕ) : WCb l) ∣ x - y → π x = π y := fun x y h => by
    rw [← sub_eq_zero, ← map_sub]; exact (hdvd _).1 h
  obtain ⟨m, hm1, hm⟩ := h2 1
  obtain ⟨R', hR'OE, hRR'⟩ := h1 m
  choose k s y hk using fun a j => hR'OE a j 1
  set N := Finset.univ.sup (fun p : Fin (d' m) × Fin d => k p.1 p.2) with hN
  have hkN : ∀ a j, k a j ≤ N := fun a j =>
    Finset.le_sup (f := fun p : Fin (d' m) × Fin d => k p.1 p.2) (Finset.mem_univ (a, j))
  let σ : Fin (d' m) → Fin d → bk.S := fun a j => X ^ (N - k a j) * s a j
  have hσ : ∀ a j, π (bk.evW (σ a j)) = π (bk.evW X ^ N * R' a j) := by
    intro a j
    have e : bk.evW X ^ N * R' a j = bk.evW (σ a j) + (l : WCb l) * (bk.evW X ^ (N - k a j) * y a j) := by
      have hk' := hk a j
      rw [pow_one] at hk'
      have hp : bk.evW X ^ N = bk.evW X ^ (N - k a j) * bk.evW X ^ k a j := by
        rw [← pow_add, Nat.sub_add_cancel (hkN a j)]
      simp only [σ, map_mul, map_pow]
      rw [hp, mul_assoc, hk']
      ring
    rw [e, map_add (f := _), (hdvd _).1 (dvd_mul_right _ _), add_zero]
  choose v hv1 hvlim using fun j => hm (fun a => σ a j)
  let V : Matrix (Fin d) (Fin d) (WCb l) := Matrix.of fun i j => v j i
  have hVmem : ∀ i j, V i j ∈ bk.OE := by
    intro i j
    apply hOEcl
    intro n
    obtain ⟨s', hs'⟩ := hvlim j n
    refine ⟨(R n *ᵥ fun a => bk.evW (s' a)) i, ?_, hs' i⟩
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun a _ => Subring.mul_mem _ (h3 n i a) (evW_mem _)
  have hπV : π.mapMatrix V = π (bk.evW X ^ N) • (1 : Matrix (Fin d) (Fin d) (WCb l ⧸ Ideal.span {((l : ℕ) : WCb l)})) := by
    ext i j
    have e1 := hdvd' _ _ (by simpa [pow_one] using hv1 j i)
    have e2 : π ((R m * R') i j) = π ((1 : Matrix (Fin d) (Fin d) (WCb l)) i j) :=
      hdvd' _ _ (dvd_trans (dvd_pow_self ((l : ℕ) : WCb l) (show m ≠ 0 by omega)) (by simpa [Matrix.sub_apply] using hRR' i j))
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, V, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [e1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hσ]
    rw [Matrix.mul_apply] at e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e2
    simp only [map_mul] at e2
    calc ∑ x, π (R m i x) * (π (bk.evW X ^ N) * π (R' x j)) = π (bk.evW X ^ N) * ∑ x, π (R m i x) * π (R' x j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by
          rw [e2]
          by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hdet : π V.det = π ((bk.evW X ^ N) ^ d) := by
    rw [RingHom.map_det, hπV, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    simp only [map_pow]
  have ndvd : ¬ ((l : ℕ) : WCb l) ∣ V.det := by
    intro h
    rw [hdvd, hdet, ← hdvd] at h
    obtain ⟨a, ha⟩ := h
    exact lnu (isUnit_of_mul_isUnit_left (ha ▸ (cU.pow N).pow d))
  let V0 : Matrix (Fin d) (Fin d) ↥bk.OE := Matrix.of fun i j => ⟨V i j, hVmem i j⟩
  have hV0 : bk.OE.subtype.mapMatrix V0 = V := by ext i j; rfl
  have hdetmem : V.det ∈ bk.OE := by
    rw [← hV0, ← RingHom.map_det]; exact (V0.det).2
  have hadj : ∀ i j, V.adjugate i j ∈ bk.OE := by
    intro i j
    rw [← hV0, ← RingHom.map_adjugate]; exact (V0.adjugate i j).2
  have hne : V.det ≠ 0 := fun h => ndvd (h ▸ dvd_zero _)
  obtain ⟨e, u, u', hu, hu', huu', hdec⟩ := hOEdec _ hdetmem hne
  have he : e = 0 := by
    by_contra he
    apply ndvd
    rw [hdec]
    obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
    exact Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero _)) _
  rw [he, pow_zero, one_mul] at hdec
  refine ⟨V, u' • V.adjugate, hVmem, fun i j => ?_, ?_, fun j k' => hvlim j k'⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]; exact Subring.mul_mem _ hu' (hadj i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, hdec, smul_smul, mul_comm, huu', one_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDualLiftingProof
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

namespace GlobalTheory.Pass.LocDual

theorem T2 {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {S S' : Submodule O M} (H : Submodule O M)
    (h : S ≤ S') : BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  unfold BlochKatoDuality.lenMod
  have hle : S ⊔ H ≤ S' ⊔ H := sup_le_sup_right h H
  let f : ↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype →ₗ[O] ↥(S' ⊔ H) ⧸ H.comap (S' ⊔ H).subtype :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (fun x hx => hx)
  refine Module.length_le_of_injective f ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker] at hz
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have := (Submodule.Quotient.mk_eq_zero _).1 hz
  exact this

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : StepLocDual := by
  intro D hLOC hBK hFont hPot i r hr Xs w hw hdeg n e hPF hLF k M hSub
  unfold LocBoundP
  apply _root_.GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset
  intro F hF
  obtain ⟨X, hX, hle⟩ := GlobalTheory.T.localCocycles_mem_span_pushout_summandLattice D hFont i r hr Xs w hw n hPF k M hSub F hF
  obtain ⟨hdrX, X', PX, hdX, hsX⟩ := GlobalTheory.T.potential_family_summand_restriction D hFont hPot i r hr Xs w hw n hPF X hX
  obtain ⟨hdrU, U', PU, hsU, LT', hdU, hrk⟩ := GlobalTheory.T.crystalline_potential_family D hFont hPot hBK i r hr Xs w hw hdeg n hPF k M hSub
  have hLift := GlobalTheory.T.liftAll_subSums_of_liftFamily_matrixFamily (Br.PD D.loc D.nbr i w hw) _ e X' U' hLF hsX hsU
  have hTw : IsTwistRep (1 : Br.G D.nbr i w hw →* (Br.LL D.nbr i w hw)ˣ)⁻¹ X.ρ X.ρ :=
    ⟨LinearEquiv.refl _ _, fun g x => by simp⟩
  have hHyp : BlochKatoDuality.Hyp (Br.PD D.loc D.nbr i w hw) X X (locU i w hw M hSub.1) X' U' 1 PX PU
      (Br.locLat D.nbr i w hw M) LT' e := ⟨hTw, hdrU, hdX, hdU, Or.inr ⟨hdrX, hLift⟩⟩
  obtain ⟨m, kk, hm, hk, hmk⟩ := hLOC.2 (D.nd.l i) (D.nbr i w hw).Kw (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)
    (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL) X X (locU i w hw M hSub.1) X' U' 1 PX PU
    (Br.locLat D.nbr i w hw M) LT' e hHyp
  refine (T2 _ hle).trans ?_
  change BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M))
    (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) ≤ _
  have hm' : BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M))
    (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) = m := hm
  have hk' : lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw) = kk := hk
  rw [hm', hk']
  have : m ≤ 2 * k * e * kk :=
    hmk.trans ((Nat.mul_le_mul_right kk (Nat.mul_le_mul_left e hrk)).trans_eq (by ring))
  exact_mod_cast this

end GlobalTheory.Pass.LocDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrincipalCongruenceFixedVectorsIff
section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp.ParInd

section Blocks
variable {R : Type} [CommRing R] {a b : ℕ}

theorem entN_tl (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin a) :
    entN M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_br (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin b) :
    entN M (a + i) (a + j) = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_self {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) : entN M i j = M i j := by
  simp [entN]

theorem det_par (M : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0) :
    M.det = (Matrix.of fun i j : Fin a => entN M i j).det *
      (Matrix.of fun i j : Fin b => entN M (a + i) (a + j)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    apply h <;> simp
  rw [h0, Matrix.det_fromBlocks_zero₂₁]
  congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, entN_tl, entN_br]

theorem exists_blocks (p : GL (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix _ _ R) i j = 0) :
    ∃ (x : GL (Fin a) R) (y : GL (Fin b) R),
      (∀ i j : Fin a, (x : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) i j) ∧
      (∀ i j : Fin b, (y : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) (a + i) (a + j)) := by
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [det_par _ h] at hu
  have h1 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hu)
  have h2 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)
  exact ⟨h1.unit, h2.unit, fun i j => by simp, fun i j => by simp⟩

def dg (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  fun i j => if (i : ℕ) < a ∧ (j : ℕ) < a then entN x i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then entN y (i - a) (j - a) else 0

theorem dg_par (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin (a + b))
    (hj : (j : ℕ) < a) (hi : a ≤ (i : ℕ)) : dg x y i j = 0 := by
  unfold dg
  rw [if_neg (by omega), if_neg (by omega)]

theorem dg_tl (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin a) :
    entN (dg x y) i j = x i j := by
  rw [entN_tl]
  simp [dg, entN_self]

theorem dg_br (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin b) :
    entN (dg x y) (a + i) (a + j) = y i j := by
  rw [entN_br]
  simp [dg, entN_self]

theorem dg_det (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) :
    (dg x y).det = x.det * y.det := by
  rw [det_par _ (dg_par x y)]
  congr 2 <;> ext i j <;> simp [dg_tl, dg_br]

theorem dg_unit (x : GL (Fin a) R) (y : GL (Fin b) R) : IsUnit (dg x.val y.val) := by
  rw [Matrix.isUnit_iff_isUnit_det, dg_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit)

end Blocks

variable {g : ℕ} [Fact g.Prime] {a b : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem inc_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (inc g n k).val = k.val.map (algebraMap ℤ_[g] ℚ_[g]) := rfl

theorem red_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (red g n k).val = k.val.map (PadicInt.toZMod (p := g)) := rfl

theorem det_inc (n : ℕ) (k : GL (Fin n) ℤ_[g]) : Matrix.GeneralLinearGroup.det (inc g n k) =
    Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, inc_val, Units.coe_map]
  exact ((algebraMap ℤ_[g] ℚ_[g]).map_det k.val).symm

variable {π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V} {σ : Representation ℂ (GL (Fin a) ℚ_[g]) W}
  {ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ} {Λ : V →ₗ[ℂ] W} {χ : (ZMod g)ˣ →* ℂˣ}

theorem blk_val (x : Gn g a) (y : Gn g b) : (blk a b (a + b) x y).val = dg x.val y.val := by
  have hu := dg_unit x y
  change (toG (dg x.val y.val)).val = _
  rw [toG, dif_pos hu, IsUnit.unit_spec]

end GlobalTheory.GLp.ParInd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyOperatorMapsIntoCompletion
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalENM

theorem EN_mem_Man : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ m ∈ P.M, P.EN m ∈ P.Man := by
  intro hB l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hS hC hH m hm
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.BK.exists_pow_E_smul_EN_mem_Man ↥(OL LL) ↥LL.1 l e a ι P
  have hv := hn m hm
  obtain ⟨jD, hjD⟩ := _root_.GlobalTheory.DeRhamIdent.main l a e _ _ (thetaW a LL) ϖ ι P T I
  let w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e := fun τ i =>
    toHat _ _ l e ⟨(E ↥LL.1 l e ^ n • P.EN m) τ i, mem_tot.1 hv τ i⟩
  have hw : ∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) =
      hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i) := fun τ i => (hat_coe_Rpi l e _).symm
  clear_value w
  have h3 := _root_.GlobalTheory.GalStep.main hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH jD hjD m hm n hv w hw
  choose y hy using fun i => _root_.GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem l a e _ _ (thetaW a LL) ϖ n (fun τ => w τ i) (h3 i)
  have hE : P.EN m ∈ P.Mext (RpiE ↥(OL LL) ↥LL.1 l e) := P.mem_Mext_invE_of_mem_divE hv
  rw [← P.hatTot_mem_Mhat_iff hE, P.mem_Mhat]
  intro τ i
  refine ⟨y i τ, ?_⟩
  have h1 := congrFun (hy i) τ
  have h2 := hw τ i
  have h4 := hat_E_pow_mul (O := ↥(OL LL)) l e n (mem_tot.1 hE τ i)

  have h1' : w τ i = Ehat ↥(OL LL) ↥LL.1 l e ^ n * y i τ := by rw [h1]; rfl
  have h5 : (E ↥LL.1 l e ^ n • P.EN m) τ i = E ↥LL.1 l e ^ n * P.EN m τ i := rfl
  have h7 := ((congrArg (algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e)) h1').symm.trans h2).trans
    ((congrArg (hat ↥(OL LL) l e) h5).trans h4)
  have h8 := (map_mul (algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)) _ _).symm.trans h7
  have hu : IsUnit (algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e ^ n)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (Ehat ↥(OL LL) ↥LL.1 l e)).pow n
  exact hu.mul_left_cancel h8

end GlobalTheory.NgalENM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]

theorem dot_add_right (ξ : ι → E) (x y : ι → Ad E) : dot ξ (x + y) = dot ξ x + dot ξ y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_add_left (ξ η : ι → E) (x : ι → Ad E) : dot (ξ + η) x = dot ξ x + dot η x := by
  simp only [dot, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem dot_zero_left (x : ι → Ad E) : dot (0 : ι → E) x = 0 := by
  simp [dot]

theorem dot_rat (ξ c : ι → E) :
    dot ξ (fun t => algebraMap E (Ad E) (c t)) = algebraMap E (Ad E) (∑ t, ξ t * c t) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dot, map_sum, map_mul]

theorem dot_single [DecidableEq ι] (t : ι) (c : E) (x : ι → Ad E) :
    dot (Pi.single t c) x = algebraMap E (Ad E) c * x t := by
  rw [dot, Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

theorem StdPsi.forall_dot_eq_one_iff {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (x : ι → Ad E) :
    (∀ ξ : ι → E, ψ (-dot ξ x) = 1) ↔ x ∈ ratV E ι := by
  classical
  constructor
  · intro h
    have hx : ∀ t, ∃ d : E, x t = algebraMap E (Ad E) d := by
      intro t
      refine hψ.ann _ fun c => ?_
      have h1 := h (Pi.single t c)
      rw [dot_single, AddChar.map_neg_eq_inv, inv_eq_one] at h1
      rwa [mul_comm]
    choose d hd using hx
    exact ⟨d, funext fun t => (hd t).symm⟩
  · rintro ⟨c, rfl⟩ ξ
    have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι) c =
        fun t => algebraMap E (Ad E) (c t) := rfl
    rw [e, dot_rat, AddChar.map_neg_eq_inv, hψ.rat, inv_one]

theorem StdPsi.per_twist {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {Φ : (ι → Ad E) → ℂ} (hΦ : Per (ratV E ι) Φ)
    (ξ : ι → E) : Per (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) := by
  refine ⟨(hψ.cont.comp (continuous_dot ξ).neg).mul hΦ.1, ?_⟩
  rintro _ ⟨c, rfl⟩ x
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι) c =
      fun t => algebraMap E (Ad E) (c t) := rfl
  have h2 := hΦ.2 _ ⟨c, rfl⟩ x
  simp only
  rw [h2, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, e, hψ.map_dot ξ c x]

theorem eq_zero_of_avg_character_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι]
    (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ →
    (∀ ξ : ι → E, avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) = 0) → Φ = 0 := by
  intro E _ _ ι _ ψ hψ Φ hΦ hco
  letI : MeasurableSpace (ι → Ad E) := borel _
  haveI : BorelSpace (ι → Ad E) := ⟨rfl⟩
  have hL := isCoLat_ratV E ι
  obtain ⟨hd, K, hK, hcov⟩ := id hL
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := _root_.GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (ι → Ad E) (ratV E ι) hL
  haveI := hd
  refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (ι → Ad E) (ratV E ι) K hK hcov (ι → E)
    (fun ξ x => ψ (-dot ξ x)) (fun ξ => hψ.cont.comp (continuous_dot ξ).neg) ?_ ?_ ?_
    (fun ξ x => hψ.norm _) (hψ.forall_dot_eq_one_iff) μ 𝓕 hμ h𝓕 Φ hΦ.1 hΦ.2 ?_
  · intro ξ x y
    rw [dot_add_right, neg_add, AddChar.map_add_eq_mul]
  · intro ξ η x
    rw [dot_add_left, neg_add, AddChar.map_add_eq_mul]
  · intro x
    rw [dot_zero_left, neg_zero, AddChar.map_zero_eq_one]
  · intro ξ
    have h2 := (_root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg (ι → Ad E) (ratV E ι) hL μ 𝓕 hμ h𝓕 _ (hψ.per_twist hΦ ξ)).2.2.2
    rw [h2, hco ξ, mul_zero]

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAddOfPeriodic
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_add_of_per : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ →
    ∀ Φ Φ' : G → ℂ, Per Γ Φ → Per Γ Φ' → avg Γ (fun x => Φ x + Φ' x) = avg Γ Φ + avg Γ Φ' := by
  intro G _ _ _ _ _ _ Γ hΓ Φ Φ' h h'
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := _root_.GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one G Γ hΓ
  have hs : Per Γ (fun x => Φ x + Φ' x) :=
    ⟨h.1.add h'.1, fun γ hγ x => by simp only [h.2 γ hγ x, h'.2 γ hγ x]⟩
  obtain ⟨-, -, i1, e1⟩ := _root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg G Γ hΓ μ 𝓕 hμ hF Φ h
  obtain ⟨-, -, i2, e2⟩ := _root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg G Γ hΓ μ 𝓕 hμ hF Φ' h'
  obtain ⟨-, -, -, e3⟩ := _root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg G Γ hΓ μ 𝓕 hμ hF _ hs
  rw [h1] at e1 e2 e3
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at e1 e2 e3
  rw [← e1, ← e2, ← e3]
  exact integral_add i1 i2

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCrystalValueMapCommFrobeniusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedCrystalValueMap_comm_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (M' : FCrys l ↥(OL K)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)) (V' : Eval S' B (M'.M B)), IsCoord e V → IsCoord e' V' → ∀ w : M.M B →ₗ[B.A] M'.M B, (∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x)) → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → IsFrac (t : B.A) (M'.Φ B t (w x)) (w m) k := by
  first | exact @GlobalTheory.BSP.eval_map_Φ | exact GlobalTheory.BSP.eval_map_Φ | (intros; apply GlobalTheory.BSP.eval_map_Φ <;> assumption)
end

