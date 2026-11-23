module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SpBasis
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private def UpperTheory.V.AlgebraTools.spIdx (n d : ℕ) (hd : d = n + 1) :
    (Fin d × ∀ i : Fin n, Fin (n - i)) ≃ (∀ i : Fin (n + 1), Fin (n + 1 - i)) where
  toFun p := fun i => Fin.cases (motive := fun i : Fin (n + 1) => Fin (n + 1 - i))
    ⟨p.1, by have := p.1.2; simp; omega⟩
    (fun j => ⟨p.2 j, by have := (p.2 j).2; simp only [Fin.val_succ]; omega⟩) i
  invFun c := (⟨c 0, by have := (c 0).2; simp at this; omega⟩,
    fun j => ⟨c j.succ, by have := (c j.succ).2; simp only [Fin.val_succ] at this; omega⟩)
  left_inv p := by
    ext <;> rfl
  right_inv c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem UpperTheory.V.AlgebraTools.spCard (n : ℕ) :
    Fintype.card (∀ i : Fin n, Fin (n - i)) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fintype.card_congr (UpperTheory.V.AlgebraTools.spIdx n (n + 1) rfl), Fintype.card_prod,
      Fintype.card_fin, ih, Nat.factorial_succ]

theorem UpperTheory.V.AlgebraTools.splitAlg_basis :
    ∀ (n : ℕ) (R : Type) [CommRing R] (P : Polynomial R), P.Monic → P.natDegree = n →
      (∃ b : Module.Basis (∀ i : Fin n, Fin (n - i)) R (SplitAlg P n), ∀ c, b c = ∏ i, SplitAlg.root P n i ^ (c i : ℕ)) ∧
      Fintype.card (∀ i : Fin n, Fin (n - i)) = n.factorial := by
  intro n
  induction n with
  | zero =>
    intro R _ P hm hd
    refine ⟨?_, UpperTheory.V.AlgebraTools.spCard 0⟩
    have hP : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    let f : SplitAlg P 0 →ₐ[R] R :=
      SplitAlg.lift P 0 (A := R) (fun i => i.elim0) (by simp [hP])
    have hfg : (Algebra.ofId R (SplitAlg P 0)).comp f = AlgHom.id R _ :=
      SplitAlg.hom_ext P 0 (fun i => i.elim0)
    have hgf : f.comp (Algebra.ofId R (SplitAlg P 0)) = AlgHom.id R R := Algebra.ext_id _ _ _
    let e : R ≃ₐ[R] SplitAlg P 0 := AlgEquiv.ofAlgHom (Algebra.ofId R _) f hfg hgf
    refine ⟨(Module.Basis.singleton (∀ i : Fin 0, Fin (0 - i)) R).map e.toLinearEquiv, fun c => ?_⟩
    simp [Module.Basis.singleton_apply]
  | succ n ih =>
    intro R _ P hm hd
    refine ⟨?_, UpperTheory.V.AlgebraTools.spCard (n + 1)⟩
    obtain ⟨inst1, inst2, h3, e, he⟩ := splitAlg_succ_equiv R n P hm hd
    have hroot : (Polynomial.map (algebraMap R (AdjoinRoot P)) P).IsRoot (AdjoinRoot.root P) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.isRoot_root P
    have hmul := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
    have hQm : (Polynomial.map (algebraMap R (AdjoinRoot P)) P /ₘ
        (Polynomial.X - Polynomial.C (AdjoinRoot.root P))).Monic := by
      refine Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C (AdjoinRoot.root P)) ?_
      rw [hmul]
      exact hm.map _
    have hQd : (Polynomial.map (algebraMap R (AdjoinRoot P)) P /ₘ
        (Polynomial.X - Polynomial.C (AdjoinRoot.root P))).natDegree = n := by
      rcases subsingleton_or_nontrivial (AdjoinRoot P) with hs | hs
      · exfalso
        have hR : Nontrivial R := by
          rcases subsingleton_or_nontrivial R with hR | hR
          · rw [Subsingleton.elim P 0, Polynomial.natDegree_zero] at hd
            omega
          · exact hR
        have hne := (AdjoinRoot.powerBasis' hm).basis.ne_zero
          ⟨0, by rw [AdjoinRoot.powerBasis'_dim, hd]; omega⟩
        exact hne (Subsingleton.elim _ _)
      · rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
          hm.natDegree_map, hd, Polynomial.natDegree_X_sub_C]
        rfl
    obtain ⟨c, hc⟩ := (ih (AdjoinRoot P) _ hQm hQd).1
    let b := (AdjoinRoot.powerBasis' hm).basis.reindex
      (finCongr (by rw [AdjoinRoot.powerBasis'_dim, hd]))
    let c' := c.map e.symm.toLinearEquiv
    refine ⟨(b.smulTower c').reindex (UpperTheory.V.AlgebraTools.spIdx n (n + 1) rfl), fun k => ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.smulTower_apply, Fin.prod_univ_succ]
    have hb : ∀ j, b j = AdjoinRoot.root P ^ (j : ℕ) := by
      intro j
      simp only [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
      rfl
    have hinv : ∀ i : Fin n, e.symm (SplitAlg.root _ n i) = SplitAlg.root P (n + 1) i.succ := by
      intro i
      rw [AlgEquiv.symm_apply_eq, he]
    simp only [c', Module.Basis.map_apply, hb, hc, Algebra.smul_def, map_pow, h3, map_prod,
      AlgEquiv.toLinearEquiv_apply, hinv]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ThetaDiag
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

section

variable {B E : Type} [CommRing B] [Ring E] [Algebra B E] {T : TrInv B E} {ι : Type} [Fintype ι]
  {o : ι → ι} (U : T.Units ι o) (p q : ι)

private def theta : E →ₗ[B] (U.oddForm p q).Ext where
  toFun z := (U.oddForm p q).el (T.tr z)
    (cornerProj B (U.ep p) (U.ep q) z + cornerProj B (U.ep p) (U.ep q) (T.st z))
  map_add' z w := by
    apply OddForm.ext
    · simp only [OddForm.ev_add]
      simp only [OddForm.Ext.ev, OddForm.el, map_add]
    · simp only [OddForm.od_add]
      simp only [OddForm.Ext.od, OddForm.el, map_add]; abel
  map_smul' c z := by
    apply OddForm.ext
    · simp only [RingHom.id_apply, OddForm.ev_smul]
      simp only [OddForm.Ext.ev, OddForm.el, map_smul, smul_eq_mul]
    · simp only [RingHom.id_apply, OddForm.od_smul]
      simp only [OddForm.Ext.od, OddForm.el, map_smul, smul_add]

private theorem theta_ev (z : E) : (theta U p q z).ev = T.tr z := rfl

private theorem theta_od (z : E) :
    (theta U p q z).od.1 = U.ep p * (z * U.ep q) + U.ep p * (T.st z * U.ep q) := rfl

private theorem theta_st (z : E) : theta U p q (T.st z) = theta U p q z := by
  apply OddForm.ext
  · rw [theta_ev, theta_ev, T.tr_st]
  · apply Subtype.ext
    rw [theta_od, theta_od, T.st_st, add_comm]

variable {p q}

private theorem theta_ep (hpq : p ≠ q) {a : ι} (ha : a = p ∨ a = q) : theta U p q (U.ep a) = 1 := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  apply OddForm.ext
  · rw [theta_ev, OddForm.ev_one, U.tr_ep]
  · apply Subtype.ext
    rw [theta_od, U.st_ep, OddForm.od_one]
    rcases ha with h | h
    · rw [h, ← mul_assoc, (U.coi.idem p).eq, hpq0]
      simp
    · rw [h, (U.coi.idem q).eq, hpq0]
      simp

private theorem theta_diag (hpq : p ≠ q) {a : ι} (ha : a = p ∨ a = q) {u : E}
    (hu : U.ep a * u * U.ep a = u) : theta U p q u = T.tr u • 1 := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hsu : U.ep a * T.st u * U.ep a = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, mul_assoc]
  have L1 : ∀ w : E, U.ep p * w * U.ep p = w → U.ep p * (w * U.ep q) = 0 := by
    intro w hw
    rw [← hw]
    simp [mul_assoc, hpq0]
  have L2 : ∀ w : E, U.ep q * w * U.ep q = w → U.ep p * (w * U.ep q) = 0 := by
    intro w hw
    rw [← hw]
    simp only [mul_assoc]
    rw [← mul_assoc (U.ep p), hpq0, zero_mul]
  apply OddForm.ext
  · rw [theta_ev, OddForm.ev_smul, OddForm.ev_one, mul_one]
  · apply Subtype.ext
    rw [theta_od, OddForm.od_smul, OddForm.od_one, smul_zero]
    rcases ha with h | h
    · rw [h] at hu hsu
      rw [L1 u hu, L1 _ hsu]
      simp
    · rw [h] at hu hsu
      rw [L2 u hu, L2 _ hsu]
      simp

private theorem theta_pq (hpq : p ≠ q) {u : E} (hu : U.ep p * u * U.ep q = u) :
    (theta U p q u).ev = 0 ∧ (theta U p q u).od.1 = u := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hqp0 : U.ep q * U.ep p = 0 := U.coi.ortho hpq.symm
  have hsu : U.ep q * T.st u * U.ep p = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [theta_ev, ← hu, T.tr_comm, ← mul_assoc, hqp0, zero_mul, map_zero]
  · have h0 : U.ep p * (T.st u * U.ep q) = 0 := by
      rw [← hsu]
      simp [mul_assoc, hpq0]
    rw [theta_od, h0, add_zero, ← mul_assoc, hu]

private theorem theta_qp (hpq : p ≠ q) {u : E} (hu : U.ep q * u * U.ep p = u) :
    (theta U p q u).ev = 0 ∧ (theta U p q u).od.1 = T.st u := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hqp0 : U.ep q * U.ep p = 0 := U.coi.ortho hpq.symm
  have hsu : U.ep p * T.st u * U.ep q = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [theta_ev, ← hu, T.tr_comm, ← mul_assoc, hpq0, zero_mul, map_zero]
  · have h0 : U.ep p * (u * U.ep q) = 0 := by
      rw [← hu]
      simp [mul_assoc, hpq0]
    rw [theta_od, h0, zero_add, ← mul_assoc, hsu]

private theorem theta_mul (hpq : p ≠ q) {a b c : ι} (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (hc : c = p ∨ c = q) {u v : E} (hu : U.ep a * u * U.ep b = u) (hv : U.ep b * v * U.ep c = v) :
    theta U p q (u * v) = theta U p q u * theta U p q v := by
  have hidem : ∀ i, U.ep i * U.ep i = U.ep i := fun i => (U.coi.idem i).eq
  have hL : ∀ {i j : ι} {w : E}, U.ep i * w * U.ep j = w → U.ep i * w = w := by
    intro i j w hw
    calc U.ep i * w = U.ep i * (U.ep i * w * U.ep j) := by rw [hw]
      _ = U.ep i * U.ep i * w * U.ep j := by simp only [mul_assoc]
      _ = w := by rw [hidem, hw]
  have hR : ∀ {i j : ι} {w : E}, U.ep i * w * U.ep j = w → w * U.ep j = w := by
    intro i j w hw
    calc w * U.ep j = U.ep i * w * U.ep j * U.ep j := by rw [hw]
      _ = U.ep i * w * (U.ep j * U.ep j) := by simp only [mul_assoc]
      _ = w := by rw [hidem, hw]
  have hsc : ∀ {i : ι} {w : E}, U.ep i * w * U.ep i = w → w = T.tr w • U.ep i := by
    intro i w hw
    have h := U.corner_eq i w
    rwa [hw] at h
  have hbe : ∀ x y, (U.oddForm p q).be x y = T.tr ((x : E) * T.st (y : E)) := fun x y => rfl
  have hleft : ∀ {i k : ι}, (i = p ∨ i = q) → U.ep i * u * U.ep i = u → U.ep i * v * U.ep k = v →
      theta U p q (u * v) = theta U p q u * theta U p q v := by
    intro i k hi hu' hv'
    have huv : u * v = T.tr u • v := by
      conv_lhs => rw [hsc hu', smul_mul_assoc, hL hv']
    rw [huv, map_smul, theta_diag U hpq hi hu', smul_mul_assoc, one_mul]
  have hright : ∀ {i k : ι}, (k = p ∨ k = q) → U.ep k * v * U.ep k = v → U.ep i * u * U.ep k = u →
      theta U p q (u * v) = theta U p q u * theta U p q v := by
    intro i k hk hv' hu'
    have huv : u * v = T.tr v • u := by
      conv_lhs => rw [hsc hv', mul_smul_comm, hR hu']
    rw [huv, map_smul, theta_diag U hpq hk hv', mul_smul_comm, mul_one]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    rw [ha, hb] at hu <;> rw [hb, hc] at hv
  · exact hleft (Or.inl rfl) hu hv
  · exact hleft (Or.inl rfl) hu hv
  · have huv : U.ep p * (u * v) * U.ep p = u * v := by
      rw [← mul_assoc, hL hu, mul_assoc, hR hv]
    rw [theta_diag U hpq (Or.inl rfl) huv]
    obtain ⟨h1, h2⟩ := theta_pq U hpq hu
    obtain ⟨h3, h4⟩ := theta_qp U hpq hv
    apply OddForm.ext
    · rw [OddForm.ev_smul, OddForm.ev_one, mul_one, OddForm.ev_mul, h1, h3, zero_mul, zero_add, hbe, h2, h4, T.st_st]
    · rw [OddForm.od_smul, OddForm.od_one, smul_zero, OddForm.od_mul, h1, h3, zero_smul, zero_smul, add_zero]
  · exact hright (Or.inr rfl) hv hu
  · exact hright (Or.inl rfl) hv hu
  · have huv : U.ep q * (u * v) * U.ep q = u * v := by
      rw [← mul_assoc, hL hu, mul_assoc, hR hv]
    rw [theta_diag U hpq (Or.inr rfl) huv]
    obtain ⟨h1, h2⟩ := theta_qp U hpq hu
    obtain ⟨h3, h4⟩ := theta_pq U hpq hv
    apply OddForm.ext
    · rw [OddForm.ev_smul, OddForm.ev_one, mul_one, OddForm.ev_mul, h1, h3, zero_mul, zero_add, hbe, h2, h4, ← T.st_mul, T.tr_st, T.tr_comm]
    · rw [OddForm.od_smul, OddForm.od_one, smul_zero, OddForm.od_mul, h1, h3, zero_smul, zero_smul, add_zero]
  · exact hleft (Or.inr rfl) hu hv
  · exact hleft (Or.inr rfl) hu hv

end

theorem UpperTheory.V.AlgebraTools.vr_hom :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p q : ι), p ≠ q → (∀ i, o i = p ∨ o i = q) → ∃ φ : E →ₐ[B] Matrix ι ι (U.oddForm p q).Ext, (∀ y, φ y = U.vr p q y) ∧ (∀ y, φ (T.st y) = (φ y)ᵀ) ∧ ∀ y, (φ y).trace = algebraMap B _ (T.tr y) := by
  intro B E _ _ _ T ι _ _ o U p q hpq ho
  obtain ⟨hA, hB, -, hD, -, -, hG⟩ := units_basic T o U
  have hvr : ∀ y i j, U.vr p q y i j = theta U p q (U.x i * y * T.st (U.x j)) := fun _ _ _ => rfl
  have hmul : ∀ y z, U.vr p q (y * z) = U.vr p q y * U.vr p q z := by
    intro y z
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply]
    simp only [hvr]
    have hs : U.x i * (y * z) * T.st (U.x j) = ∑ k, (U.x i * y * T.st (U.x k)) * (U.x k * z * T.st (U.x j)) := by
      calc U.x i * (y * z) * T.st (U.x j) = U.x i * y * (∑ k, T.st (U.x k) * U.x k) * z * T.st (U.x j) := by
            rw [hB, mul_one, mul_assoc (U.x i) y z]
        _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact theta_mul U hpq (ho i) (ho k) (ho j) (hG i k y) (hG k j z)
  have hone : U.vr p q 1 = 1 := by
    refine Matrix.ext fun i j => ?_
    rw [hvr, mul_one, Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [U.x_st]
      exact theta_ep U hpq (ho i)
    · rw [hA i j h, map_zero]
  have hadd : ∀ y z, U.vr p q (y + z) = U.vr p q y + U.vr p q z := by
    intro y z
    refine Matrix.ext fun i j => ?_
    simp only [hvr, Matrix.add_apply, mul_add, add_mul, map_add (f := _)]
  have hzero : U.vr p q 0 = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [hvr, mul_zero, zero_mul, map_zero, Matrix.zero_apply]
  have hsmul : ∀ (r : B) y, U.vr p q (r • y) = r • U.vr p q y := by
    intro r y
    refine Matrix.ext fun i j => ?_
    simp only [hvr, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul]
  have hcomm : ∀ r : B, U.vr p q (algebraMap B E r) = algebraMap B (Matrix ι ι (U.oddForm p q).Ext) r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hsmul, hone]
  have hst : ∀ y, U.vr p q (T.st y) = (U.vr p q y)ᵀ := by
    intro y
    refine Matrix.ext fun i j => ?_
    rw [Matrix.transpose_apply, hvr, hvr, ← theta_st U p q (U.x j * y * T.st (U.x i)), T.st_mul, T.st_mul, T.st_st, mul_assoc]
  have htr : ∀ y, (U.vr p q y).trace = algebraMap B _ (T.tr y) := by
    intro y
    rw [Matrix.trace, Algebra.algebraMap_eq_smul_one, hD y, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, hvr]
    exact theta_diag U hpq (ho i) (hG i i y)
  let φ : E →ₐ[B] Matrix ι ι (U.oddForm p q).Ext := { toFun := U.vr p q, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := hadd, commutes' := hcomm }
  exact ⟨φ, fun y => rfl, hst, htr⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnIdem
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_idem_topNil :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      ∃ e ∈ Algebra.adjoin R (Set.range T), IsIdempotentElem e ∧ LinearMap.range e = topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ _ T hT
  classical
  let S := Algebra.adjoin R (Set.range T)
  have : Module.Finite R S := by
    have : IsNoetherian R (Subalgebra.toSubmodule S) := inferInstance
    exact (inferInstance : Module.Finite R (Subalgebra.toSubmodule S))
  have : IsMulCommutative S := Algebra.isMulCommutative_adjoin R (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hT i j)
  let _ : CommRing S := by
    open scoped IsMulCommutative in
    exact inferInstance
  let t : κ → S := fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  obtain ⟨e, he, -, hx⟩ := topNil_eq_idem R S κ t
  have hfun : (fun i => (Algebra.lsmul R R M) (t i)) = T := by
    funext i
    rfl
  have he' : IsIdempotentElem (e : Module.End R M) := congrArg Subtype.val he
  refine ⟨(e : Module.End R M), e.2, he', ?_⟩
  ext x
  have h := hx M x
  rw [hfun] at h
  rw [h]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun he' y
  · intro h2
    exact ⟨x, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimConst
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.const_bijective :
    ∀ (R ι : Type) [CommRing R] (U : Ultrafilter ι) (m : Ideal R) (Z : Type) [AddCommGroup Z] [Module R Z], IsAdicComplete m Z →
      (∀ j : ℕ, Finite (Z ⧸ (m ^ j • ⊤ : Submodule R Z))) →
      Function.Bijective fun z : Z => ULim.mk (U : Filter ι) (fun j => m ^ j) (fun _ => Z) fun _ => z := by
  intro R ι _ U m Z _ _ hc hfin
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : ULim.mk (U : Filter ι) (fun j => m ^ j) (fun _ => Z) (fun _ => a - b) = 0 := by
      have h1 : (fun _ : ι => a - b) = (fun _ : ι => a) - (fun _ : ι => b) := rfl
      rw [h1, map_sub]
      exact sub_eq_zero.2 hab
    rw [ULim.mk_eq_zero] at h0
    refine sub_eq_zero.1 (IsHausdorff.haus hc.toIsHausdorff _ fun j => ?_)
    obtain ⟨_, h⟩ := (h0 j).exists
    exact SModEq.zero.2 h
  · obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ x
    have hz : ∀ j : ℕ, ∃ z : Z, ∀ᶠ i in (U : Filter ι), p i ≡ z [SMOD (m ^ j • ⊤ : Submodule R Z)] := by
      intro j
      haveI := hfin j
      obtain ⟨q, hq⟩ := Ultrafilter.eq_pure_of_finite
        (U.map fun i => (Submodule.Quotient.mk (p i) : Z ⧸ (m ^ j • ⊤ : Submodule R Z)))
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨z, ?_⟩
      have h : ({Submodule.Quotient.mk z} : Set (Z ⧸ (m ^ j • ⊤ : Submodule R Z))) ∈
          U.map fun i => (Submodule.Quotient.mk (p i) : Z ⧸ (m ^ j • ⊤ : Submodule R Z)) := by
        rw [hq]; simp
      exact h
    choose z hz using hz
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := z) (fun {j k} hjk => by
      obtain ⟨i, h1, h2⟩ := ((hz j).and (hz k)).exists
      exact h1.symm.trans (h2.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hjk))))
    refine ⟨L, ?_⟩
    show ULim.mk _ _ _ _ = _
    rw [← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]
    intro j
    refine (hz j).mono fun i hi => ?_
    exact SModEq.sub_mem.1 (hi.trans (hL j)).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimScal
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.scal_eq :
    ∀ (R ι : Type) [CommRing R] (F : Filter ι) (I : ℕ → Ideal R) (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
      (∀ (r : ι → R) (s : R), (∀ j, ∀ᶠ N in F, ∀ x : M N, (r N - s) • x ∈ (I j • ⊤ : Submodule R (M N))) →
        ∀ x : ULim F I M, ULim.scal F I M r x = s • x) ∧
      (∀ s : R, (∀ j, ∀ᶠ N in F, ∀ x : M N, s • x ∈ (I j • ⊤ : Submodule R (M N))) → ∀ x : ULim F I M, s • x = 0) ∧
      (∀ (M' : ι → Type) [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M i →ₗ[R] M' i) (g : ∀ i, M' i →ₗ[R] M i) (r : ι → R), (∀ i x, g i (f i x) = r i • x) →
        ∀ x : ULim F I M, ULim.map F (fun _ => le_rfl) g (ULim.map F (I' := I) (fun _ => le_rfl) f x) = ULim.scal F I M r x) := by
  intro R ι _ F I M _ _
  have hs : ∀ (r : ι → R) (p : ∀ i, M i), ULim.scal F I M r (ULim.mk F I M p) = ULim.mk F I M (fun i => r i • p i) := by
    intro r p
    simp only [ULim.scal, ULim.map_mk, LinearMap.smul_apply, LinearMap.id_apply]
  have hc : ∀ (s : R) (p : ∀ i, M i), s • ULim.mk F I M p = ULim.mk F I M (fun i => s • p i) := by
    intro s p
    rw [← map_smul]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro r s h x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [← sub_eq_zero, hs, hc, ← map_sub, ULim.mk_eq_zero]
    intro j
    filter_upwards [h j] with N hN
    simpa [sub_smul] using hN (p N)
  · intro s h x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [hc, ULim.mk_eq_zero]
    intro j
    filter_upwards [h j] with N hN
    exact hN (p N)
  · intro M' _ _ f g r hfg x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [ULim.map_mk, ULim.map_mk, hs]
    simp only [hfg]
end

