module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bundle0001
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.CoefProd
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.UnitColsZero
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.EvalIdFrameRowAct
public import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial

@[expose] public section

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FinalTheorems
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.MainNotions.G

def evX {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) : GenR K n →+* MvPolynomial (Fin n × Fin n) K :=
  eval₂Hom (RingHom.id _) fun s => C (x s)

section FinalTheorems

variable {O K Kc : Type} [CommRing O] [Field K] [Algebra O K] [Infinite K] [Field Kc] [Algebra K Kc]
  {B τ τx : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (xm : B → ℕ × Fin n → τx) (hxm : Function.Injective fun x : B × (ℕ × Fin n) => xm x.1 x.2)
  (ν : B → Fin n → ℕ)
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc) (hM : ∀ (o : O), ∀ a ∈ M, algebraMap K Kc (algebraMap O K o) * a ∈ M)
  (Hg : B → GenR K n)
  (hQ : ∀ b, (weyl O n n le_rfl (ν b)).map (toK O K) ≤ Submodule.span O (Set.range fun m => AddMonoidAlgebra.coeff (Hg b) m))
  (Φ : MvPolynomial τ K →ₗ[K] Kc) (A : MvPolynomial τx Kc) (hA : ∀ m, AddMonoidAlgebra.coeff A m ∈ M)
  (hnum : ∀ x : τx → K, Φ (∏ b, rename (em b) (rowAct K (hi b) (evX (fun s => x (xm b s)) (Hg b)))) =
    eval (fun t => algebraMap K Kc (x t)) A)


include hxm hh hM hQ hA hnum in
theorem src_abs (hI : Interp) (hCP : CoefProd) (F : B → MvPolynomial (Fin n × Fin n) K)
    (hF : ∀ b, F b ∈ deltaL O K n (ν b) (h b)) : Φ (∏ b, rename (em b) (F b)) ∈ M := by
  classical
  have hh' : ∀ b, h b * hi b = 1 := fun b => mul_eq_one_comm.1 (hh b)
  let ψ : ∀ b, MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial τ K := fun b => (rename (em b)).comp (rowAct K (hi b))
  let HH : MvPolynomial τx (MvPolynomial τ K) := ∏ b, rename (xm b) (map (ψ b : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial τ K) (Hg b))
  have hcoef : ∀ p : B → (ℕ × Fin n →₀ ℕ), AddMonoidAlgebra.coeff HH (∑ b, (p b).mapDomain (xm b)) = ∏ b, ψ b (AddMonoidAlgebra.coeff (Hg b) (p b)) := by
    intro p
    rw [hCP (MvPolynomial τ K) B (ℕ × Fin n) τx xm hxm]
    exact Finset.prod_congr rfl fun b _ => coeff_map _ _ _
  have hev : ∀ x : τx → K, eval₂ (RingHom.id (MvPolynomial τ K)) (fun t => C (x t)) HH =
      ∏ b, rename (em b) (rowAct K (hi b) (evX (fun s => x (xm b s)) (Hg b))) := by
    intro x
    show eval₂Hom (RingHom.id (MvPolynomial τ K)) (fun t => C (x t)) HH = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [coe_eval₂Hom, eval₂_rename, eval₂_map]
    show _ = ψ b (eval₂ (RingHom.id _) (fun s => C (x (xm b s))) (Hg b))
    rw [← AlgHom.coe_toRingHom, eval₂_comp_left]
    congr 1
    funext s
    show C (x (xm b s)) = ψ b (C (x (xm b s)))
    exact ((ψ b).commutes (x (xm b s))).symm
  have hw : ∀ m, Φ (AddMonoidAlgebra.coeff HH m) = AddMonoidAlgebra.coeff A m := by
    intro m
    by_cases hm : m ∈ HH.support ∪ A.support
    · have := hI K τx Kc (HH.support ∪ A.support) (fun m => Φ (AddMonoidAlgebra.coeff HH m) - AddMonoidAlgebra.coeff A m) ?_ m hm
      · exact sub_eq_zero.1 this
      · intro x
        simp only [smul_sub]
        rw [Finset.sum_sub_distrib, sub_eq_zero]
        have e1 : ∑ m ∈ HH.support ∪ A.support, (m.prod fun t k => x t ^ k) • Φ (AddMonoidAlgebra.coeff HH m) =
            Φ (eval₂ (RingHom.id (MvPolynomial τ K)) (fun t => C (x t)) HH) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [eval₂_eq, map_sum, ← Finset.sum_subset Finset.subset_union_left]
          · refine Finset.sum_congr rfl fun d _ => ?_
            rw [← map_smul]
            congr 1
            rw [RingHom.id_apply, smul_eq_C_mul, mul_comm, Finsupp.prod, map_prod]
            simp only [map_pow]
          · intro d _ hd
            rw [notMem_support_iff.1 hd, map_zero, smul_zero]
        have e2 : ∑ m ∈ HH.support ∪ A.support, (m.prod fun t k => x t ^ k) • AddMonoidAlgebra.coeff A m =
            eval (fun t => algebraMap K Kc (x t)) A := by
          rw [eval_eq, ← Finset.sum_subset Finset.subset_union_right]
          · refine Finset.sum_congr rfl fun d _ => ?_
            rw [Algebra.smul_def, mul_comm, Finsupp.prod, map_prod]
            simp only [map_pow]
          · intro d _ hd
            rw [notMem_support_iff.1 hd, smul_zero]
        rw [e1, e2, hev, hnum]
    · rw [Finset.mem_union, not_or] at hm
      rw [notMem_support_iff.1 hm.1, notMem_support_iff.1 hm.2, map_zero]
  let T : Submodule O (MvPolynomial τ K) :=
    { carrier := {G | Φ G ∈ M}
      add_mem' := fun {a b} ha hb => by
        show Φ (a + b) ∈ M
        rw [map_add (f := _)]; exact M.add_mem ha hb
      zero_mem' := by show Φ 0 ∈ M; rw [map_zero]; exact M.zero_mem
      smul_mem' := fun o G hG => by
        show Φ (o • G) ∈ M
        rw [← algebraMap_smul K o G, map_smul, Algebra.smul_def]
        exact hM o _ hG }
  refine prod_span (R := O) (fun b => Set.range fun m => ψ b (AddMonoidAlgebra.coeff (Hg b) m)) T ?_ _ ?_
  · intro f hf
    choose p hp using hf
    show Φ _ ∈ M
    rw [← Finset.prod_congr rfl fun b _ => hp b, ← hcoef, hw]
    exact hA _
  · intro b
    have h2 : rowAct K (h b) (F b) ∈ Submodule.span O (Set.range fun m => AddMonoidAlgebra.coeff (Hg b) m) := hQ b (hF b)
    have h3 : rename (em b) (F b) = ψ b (rowAct K (h b) (F b)) := by
      show _ = rename (em b) (rowAct K (hi b) (rowAct K (h b) (F b)))
      rw [rowAct_rowAct, hh' b, rowAct_one]
    rw [h3]
    have h4 := Submodule.mem_map_of_mem (f := (ψ b).toLinearMap.restrictScalars O) h2
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact h4

end FinalTheorems

end Formalism.L2.PairingIndexBounds.Ent
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HighestVectorFullHolds
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

namespace UnitColumnMinors

theorem minor_zero (A : Type) [CommRing A] (r n s : ℕ) (hs : s ≤ n) (I : Fin s → Fin r)
    (hI : ¬ Function.Injective I) : initMinor A I hs = 0 := by
  simp only [Function.Injective, not_forall] at hI
  obtain ⟨a, b, hab, hne⟩ := hI
  unfold initMinor
  exact Matrix.det_zero_of_row_eq hne (by funext q; simp only [Matrix.of_apply, hab])

open Classical in
theorem unit_cols (n l : ℕ) (hl : l ≤ n) (I : Fin (n - l) → Fin n) (hI : Function.Injective I) :
    ∃ (J : Fin l → Fin n) (ε : ℤ), Function.Injective J ∧ (∀ i q, J i ≠ I q) ∧ (ε = 1 ∨ ε = -1) ∧
      ∀ (A : Type) [CommRing A] (z : Fin n → ℕ → A),
        (catM l (unitM A I) z).det = (ε : A) * (Matrix.of fun i i' : Fin l => z (J i') i.val).det := by
  have hm : n - l ≤ n := Nat.sub_le n l
  let e0 : {a : Fin n // a.val < n - l} ≃ {b : Fin n // b ∈ Set.range I} :=
    Equiv.ofBijective (fun a => ⟨I ⟨a.1.val, a.2⟩, ⟨_, rfl⟩⟩)
      ⟨fun a b h => by
        have := hI (congrArg Subtype.val h)
        exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val this)),
       fun b => by
        obtain ⟨b, ⟨q, rfl⟩⟩ := b
        exact ⟨⟨Fin.castLE hm q, q.isLt⟩, rfl⟩⟩
  let π : Equiv.Perm (Fin n) := e0.extendSubtype
  have hπ : ∀ q : Fin (n - l), π (Fin.castLE hm q) = I q := fun q =>
    e0.extendSubtype_apply_of_mem (Fin.castLE hm q) q.isLt
  let J : Fin l → Fin n := fun i => π ⟨n - l + i.val, by have := i.isLt; omega⟩
  refine ⟨J, ((Equiv.Perm.sign π : ℤˣ) : ℤ), ?_, ?_, ?_, ?_⟩
  · intro i i' h
    have h1 := Fin.mk.inj (π.injective h)
    exact Fin.ext (by omega)
  · intro i q h
    have h1 : J i = π (Fin.castLE hm q) := by rw [hπ]; exact h
    have h2 := congrArg Fin.val (π.injective h1)
    simp only [Fin.val_castLE] at h2
    have := q.isLt
    omega
  · rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · left; rw [h]; rfl
    · right; rw [h]; rfl
  · intro A _ z
    have key : (catM l (unitM A I) z).submatrix π id =
        catM l ((1 : A) • (1 : Matrix (Fin n) (Fin n) A)) (fun a i => z (π a) i) := by
      ext a t
      simp only [Matrix.submatrix_apply, id, catM]
      split_ifs with ht
      · simp only [unitM, dif_pos ht, one_smul, Matrix.one_apply]
        rw [← hπ ⟨t.val, ht⟩]
        have : Fin.castLE hm ⟨t.val, ht⟩ = t := Fin.ext rfl
        simp only [Equiv.apply_eq_iff_eq, this]
      · rfl
    have h1 := Matrix.det_permute π (catM l (unitM A I) z)
    rw [key, det_catM_smul_one l hl, one_pow, one_mul] at h1
    have h2 : (Matrix.of fun i i' : Fin l => z (J i') i.val).det = lastMinor l hl (fun a i => z (π a) i) := by
      unfold lastMinor
      rw [← Matrix.det_transpose]
      rfl
    have hs : (((Equiv.Perm.sign π : ℤˣ) : ℤ) : A) * (((Equiv.Perm.sign π : ℤˣ) : ℤ) : A) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    rw [h2, h1, ← mul_assoc, hs, one_mul]

theorem hv_full (A : Type) [CommRing A] (n : ℕ) (μ : Fin n → ℕ) (hμ : Antitone μ) (c e : ℕ) (hc : ∀ t, μ t ≤ c)
    (he : ∀ t, e ≤ μ t) (hl : ∀ t : Fin n, t.val + 1 = n → μ t = e) (hn : 0 < n) (x : Fin n → ℕ → A)
    (y : Matrix (Fin n) (Fin n) A) :
    hvE x y c (fun k => colH μ k.val) (fun k => colH_le μ k.val) =
      ((Matrix.of fun a i : Fin n => x a i.val).det * y.det) ^ e *
        hvE x y c (fun k => colH (fun t => μ t - e) k.val) (fun k => colH_le _ k.val) := by
  let F : ℕ → A := fun m =>
    if h : m ≤ n then (Matrix.of fun i t : Fin m => ∑ a, x a i.val * y a (Fin.castLE h t)).det else 1
  have hF : F 0 = 1 := by
    simp only [F, Nat.zero_le, dif_pos]
    exact Matrix.det_isEmpty
  have hE : ∀ ν : Fin n → ℕ, hvE x y c (fun k => colH ν k.val) (fun k => colH_le ν k.val) =
      ∏ k : Fin c, F (colH ν k.val) := by
    intro ν
    unfold hvE
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [F, dif_pos (colH_le ν k.val)]
  have hμ' : Antitone fun t => μ t - e := fun a b h => by
    have := hμ h
    simp only
    omega
  have hc' : ∀ t, μ t - e ≤ c := fun t => (Nat.sub_le _ _).trans (hc t)
  rw [hE, hE, BidetPairing.prod_colH hμ c hc F hF, BidetPairing.prod_colH hμ' c hc' F hF]
  have hFn : F n = (Matrix.of fun a i : Fin n => x a i.val).det * y.det := by
    simp only [F]
    rw [dif_pos le_rfl, ← Matrix.det_transpose (Matrix.of fun a i : Fin n => x a i.val), ← Matrix.det_mul]
    congr 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  have hlast : μ (Fin.last m) = e := hl _ (by simp)
  have hn1 : ∀ ν : Fin (m + 1) → ℕ, nuNext ν (Fin.last m) = 0 := fun ν => by
    unfold nuNext
    simp
  have hn2 : ∀ (ν : Fin (m + 1) → ℕ) (i : Fin m), nuNext ν i.castSucc = ν i.succ := fun ν i => by
    unfold nuNext
    rw [dif_pos (by simp)]
    rfl
  have hexp : ∀ i : Fin m, (μ i.castSucc - e) - (μ i.succ - e) = μ i.castSucc - μ i.succ := fun i => by
    have := he i.castSucc
    have := he i.succ
    omega
  simp only [hn1, hn2, hexp, hlast, Nat.sub_zero, Nat.sub_self, pow_zero, mul_one, Fin.val_last]
  rw [hFn]
  ring

theorem mem_dualWeyl_of_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    {r n : ℕ} {ν : Fin n → ℕ} (f : MvPolynomial (Fin r × Fin n) R) (h : map φ f ∈ dualWeyl S r n ν) :
    f ∈ dualWeyl R r n ν := by
  rw [lsat_mem_dualWeyl] at h ⊢
  obtain ⟨hh, hk⟩ := h
  refine ⟨?_, ?_⟩
  · intro d hd
    apply hh
    rw [coeff_map]
    exact (map_ne_zero_iff φ hφ).2 hd
  · intro l j hlj
    apply MvPolynomial.map_injective φ hφ
    rw [lsat_map_colAddGen, hk l j hlj, map_rename]

end UnitColumnMinors

open UnitColumnMinors

theorem minor_zero_holds : MinorZero := fun A _ r n s hs I hI => minor_zero A r n s hs I hI

theorem unit_columns_holds : UnitCols := fun n l hl I hI => unit_cols n l hl I hI

theorem highest_vector_full_holds : HvFull := fun A _ n μ hμ c e hc he hl hn x y => hv_full A n μ hμ c e hc he hl hn x y

theorem highest_vector_mem_even : HvMemE := by
  intro K _ _ n ν hν c hc x
  rw [BidetPairing.hvE_eq K n ν hν c hc x]
  exact dualWeylRowStable K n n ν _ _ (hwMem K n n le_rfl ν hν)

theorem highest_vector_mem_odd : HvMemO := by
  intro K _ _ n μ hμ c hc x
  have hι : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) K)
      (FractionRing (MvPolynomial (Fin n × Fin n) K))) :=
    IsFractionRing.injective _ _

  let xg : Fin n → ℕ → MvPolynomial (Fin n × Fin n) K :=
    fun a i => if h : i < n then X (a, ⟨n - 1 - i, by omega⟩) else 0
  have hXg : (Matrix.of fun a t : Fin n => xg a (n - 1 - t.val)) = Matrix.mvPolynomialX (Fin n) (Fin n) K := by
    ext a t
    have := t.isLt
    simp only [Matrix.of_apply, xg, Matrix.mvPolynomialX_apply, dif_pos (show n - 1 - t.val < n by omega)]
    apply congrArg (fun p : Fin n × Fin n => (X p : MvPolynomial (Fin n × Fin n) K).coeff _)
    refine Prod.ext rfl (Fin.ext ?_)
    show n - 1 - (n - 1 - t.val) = t.val
    omega
  let XL : Matrix (Fin n) (Fin n) (FractionRing (MvPolynomial (Fin n × Fin n) K)) :=
    Matrix.of fun a t : Fin n => algebraMap _ _ (xg a (n - 1 - t.val))
  have hdet : XL.det ≠ 0 := by
    have hXL : XL = (Matrix.mvPolynomialX (Fin n) (Fin n) K).map
        (algebraMap (MvPolynomial (Fin n × Fin n) K) (FractionRing (MvPolynomial (Fin n × Fin n) K))) := by
      rw [← hXg]
      rfl
    rw [hXL, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h0
    exact Matrix.det_mvPolynomialX_ne_zero (Fin n) K (hι (by rw [h0, map_zero]))
  have hU : IsUnit XL.det := isUnit_iff_ne_zero.2 hdet
  have hgen : hvO (fun a i => C (algebraMap (MvPolynomial (Fin n × Fin n) K)
      (FractionRing (MvPolynomial (Fin n × Fin n) K)) (xg a i)))
        (yV (FractionRing (MvPolynomial (Fin n × Fin n) K)) n) c (fun k => colH μ k.val) ∈
      dualWeyl (FractionRing (MvPolynomial (Fin n × Fin n) K)) n n (fun t : Fin n => c - μ t.rev) := by
    rw [BidetPairing.hvO_eq_inv (FractionRing (MvPolynomial (Fin n × Fin n) K)) n μ hμ c hc
      (fun a i => algebraMap _ _ (xg a i)) XL⁻¹ (Matrix.nonsing_inv_mul XL hU) (Matrix.mul_nonsing_inv XL hU), C_mul']
    exact Submodule.smul_mem _ _
      (dualWeylRowStable _ n n _ _ _ (hwMem _ n n le_rfl _ (BidetPairing.kap_antitone hμ c)))
  rw [← BidetPairing.map_hvO' (algebraMap (MvPolynomial (Fin n × Fin n) K)
      (FractionRing (MvPolynomial (Fin n × Fin n) K))) xg c (fun k => colH μ k.val)] at hgen
  have hS := mem_dualWeyl_of_map _ hι _ hgen
  have hK := dualWeylMap (MvPolynomial (Fin n × Fin n) K) K (eval fun v : Fin n × Fin n => x v.1 (n - 1 - v.2.val))
    n n _ _ hS
  rw [BidetPairing.map_hvO'] at hK
  have hx : ∀ a i, i < n → (fun a i => C (x a i) : Fin n → ℕ → MvPolynomial (Fin n × Fin n) K) a i =
      (fun a i => C (eval (fun v : Fin n × Fin n => x v.1 (n - 1 - v.2.val)) (xg a i))) a i := by
    intro a i hi
    simp only [xg, dif_pos hi, eval_X]
    congr 2
    omega
  convert hK using 1
  unfold hvO
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [BidetPairing.catM_congr _ _ _ _ hx]

end Formalism.L2.PairingIndexBounds.Ent
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.TgtBidet
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.MainNotions.G

variable {O K Kc : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [CharZero K] [Field Kc] [Algebra K Kc]
  {B τ : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (hem : Function.Injective fun x : B × (Fin n × Fin n) => em x.1 x.2)
  (ν : B → Fin n → ℕ) (hν : ∀ b, Antitone (ν b))
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc) (hM : ∀ (o : O), ∀ a ∈ M, algebraMap K Kc (algebraMap O K o) * a ∈ M)

theorem toK_bidet {r n K' : ℕ} (sz : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    toK O K (bideterminant O sz hsz I) = bideterminant K sz hsz I := by
  show map (algebraMap O K) _ = _
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp


include hem hν hh hM in
theorem tgt_bidet (hDB : DualBases) (hFP : FockProd) (hRe : Reorder) (c : B → ℕ) (sz : ∀ b, Fin (c b) → ℕ)
    (hsz : ∀ b k, sz b k ≤ n) (hshape : ∀ b, shapeDeg (sz b) = ν b) (y : MvPolynomial τ Kc)
    (hy : y ∈ Submodule.span Kc {z | ∃ F : B → MvPolynomial (Fin n × Fin n) K, (∀ b, F b ∈ dualWeyl K n n (ν b)) ∧
      z = map (algebraMap K Kc) (∏ b, rename (em b) (F b))})
    (hp : ∀ I : ∀ b, ∀ k, Fin (sz b k) → Fin n,
      ∃ a ∈ M, fockR y (map (algebraMap K Kc) (∏ b, rename (em b) (rowAct K (h b).transpose (bideterminant K (sz b) (hsz b) (I b))))) =
        a * ∏ b, cN Kc (ν b)) :
    y ∈ AddSubgroup.closure {z | ∃ a ∈ M, ∃ F : B → MvPolynomial (Fin n × Fin n) K,
      (∀ b, F b ∈ deltaL O K n (ν b) (h b)) ∧ z = a • map (algebraMap K Kc) (∏ b, rename (em b) (F b))} := by
  refine tgt_abs (O := O) em hem ν hν h hi hh M hDB hFP y hy fun Q hQ => ?_
  let T : Submodule O (MvPolynomial τ K) :=
    { carrier := {Z | ∃ a ∈ M, fockR y (map (algebraMap K Kc) Z) = a * ∏ b, cN Kc (ν b)}
      add_mem' := by
        rintro Z Z' ⟨a, ha, h1⟩ ⟨a', ha', h2⟩
        refine ⟨a + a', M.add_mem ha ha', ?_⟩
        rw [map_add (f := _), fockR_comm, fockR_add_left, fockR_comm _ y, fockR_comm _ y, h1, h2, add_mul]
      zero_mem' := ⟨0, M.zero_mem, by rw [map_zero, fockR_comm, fockR_zero_left, zero_mul]⟩
      smul_mem' := by
        rintro o Z ⟨a, ha, h1⟩
        refine ⟨_, hM o a ha, ?_⟩
        rw [← algebraMap_smul K o Z, smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, fockR_comm, fockR_smul_left, fockR_comm, h1,
          mul_assoc] }
  refine prod_span (R := O) (fun b => Set.range fun I : ∀ k, Fin (sz b k) → Fin n =>
    rename (em b) (rowAct K (h b).transpose (bideterminant K (sz b) (hsz b) I))) T ?_ _ ?_
  · intro f hf
    choose I hI using hf
    obtain ⟨a, ha, h1⟩ := hp I
    refine ⟨a, ha, ?_⟩
    rw [← Finset.prod_congr rfl fun b _ => hI b]
    exact h1
  · intro b
    have h1 := hQ b
    rw [standardMonomialSpanDomain O n n (ν b), Submodule.map_span] at h1
    have h2 := Submodule.mem_map_of_mem (f := (((rename (em b) : MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial τ K).comp
      (rowAct K (h b).transpose)).toLinearMap).restrictScalars O) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨_, ⟨K', sz', hsz', I', hs', rfl⟩, rfl⟩, rfl⟩
    obtain ⟨I'', hI''⟩ := hRe K n n K' (c b) sz' (sz b) hsz' (hsz b) (hs'.trans (hshape b).symm) I'
    refine ⟨I'', ?_⟩
    rw [toK_bidet, hI'']
    rfl

end Formalism.L2.PairingIndexBounds.Ent
end
end

