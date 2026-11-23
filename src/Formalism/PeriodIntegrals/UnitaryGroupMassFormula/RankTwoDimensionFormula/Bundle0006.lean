module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDMatP
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mat_idem_mul {Rg : Type} [Ring Rg] (E a b : Rg) (hE : E * E = E) (hc : ∀ x : Rg, E * x = x * E) :
    (E * a + (1 - E)) * (E * b + (1 - E)) = E * (a * b) + (1 - E) := by
  have h1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h3 : (1 - E) * (1 - E) = 1 - E := by rw [sub_mul, one_mul, h1, sub_zero]
  have e1 : E * a * (E * b) = E * (a * b) := by
    rw [mul_assoc, ← mul_assoc a E b, ← hc a, ← mul_assoc, ← mul_assoc, hE, mul_assoc]
  have e2 : E * a * (1 - E) = 0 := by
    have : a * (1 - E) = (1 - E) * a := by rw [mul_sub, sub_mul, mul_one, one_mul, hc a]
    rw [mul_assoc, this, ← mul_assoc, h1, zero_mul]
  have e3 : (1 - E) * (E * b) = 0 := by rw [← mul_assoc, h2, zero_mul]
  rw [add_mul, mul_add, mul_add, e1, e2, e3, h3, add_zero, zero_add]

theorem mat_lift_core {O : Type} [CommRing O] {k : ℕ} (gO eO wO : O) (he2 : eO * eO = eO) (hw2 : wO * wO = wO)
    (Mo No tt : Matrix (Fin k) (Fin k) O) (htt : ∀ i j, wO * (No * Mo - 1) i j = gO * tt i j)
    (hJ : ∀ m : O, ∃ y : O, eO * (1 + gO * m) * y = eO) :
    ∃ C C' : Matrix (Fin k) (Fin k) O, C' * C = 1 ∧ ∀ i j, (eO * wO) * C i j = (eO * wO) * Mo i j := by
  set Q : Matrix (Fin k) (Fin k) O := 1 + gO • tt with hQdef
  obtain ⟨m, hm⟩ : ∃ m : O, Q.det = 1 + gO * m := by
    have hQ : (Ideal.Quotient.mk (Ideal.span {gO})).mapMatrix Q = 1 := by
      have hπg : Ideal.Quotient.mk (Ideal.span {gO}) gO = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [hQdef, map_add (f := _), map_one]
      ext i j
      simp [hπg]
    have h1 : Ideal.Quotient.mk (Ideal.span {gO}) (Q.det - 1) = 0 := by
      rw [map_sub, RingHom.map_det, hQ, det_one, map_one, sub_self]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    refine ⟨a, ?_⟩
    rw [mul_comm, ha]; ring
  obtain ⟨yO, hey0⟩ := hJ m
  have hey : eO * Q.det * yO = eO := by rw [hm]; exact hey0
  set εO := eO * wO with hεdef
  set E : Matrix (Fin k) (Fin k) O := εO • 1 with hEdef
  have hEc : ∀ x : Matrix (Fin k) (Fin k) O, E * x = x * E := by
    intro x; simp [hEdef]
  have hε2 : εO * εO = εO := by
    calc εO * εO = (eO * eO) * (wO * wO) := by rw [hεdef]; ring
      _ = εO := by rw [he2, hw2]
  have hE2 : E * E = E := by simp [hEdef, smul_smul, hε2]
  have hEQ : E * (No * Mo) = E * Q := by
    ext i j
    simp only [hEdef, Matrix.smul_mul, one_mul, Matrix.smul_apply, smul_eq_mul, hQdef, Matrix.add_apply]
    have h1 : (No * Mo) i j = (No * Mo - 1) i j + (1 : Matrix (Fin k) (Fin k) O) i j := by
      rw [Matrix.sub_apply]; ring
    have h2 : wO * (gO * tt i j) = gO * tt i j := by
      rw [← htt i j, ← mul_assoc, hw2]
    have key : εO * (No * Mo - 1) i j = εO * (gO • tt) i j := by
     calc εO * (No * Mo - 1) i j = eO * (wO * (No * Mo - 1) i j) := by rw [hεdef]; ring
      _ = eO * (wO * (gO * tt i j)) := by rw [htt i j, h2]
      _ = εO * (gO * tt i j) := by rw [hεdef]; ring
      _ = εO * (gO • tt) i j := by rw [Matrix.smul_apply, smul_eq_mul]
    rw [h1, mul_add, mul_add, key, Matrix.smul_apply, smul_eq_mul]; ring
  set P : Matrix (Fin k) (Fin k) O := yO • Q.adjugate with hPdef
  have hEPQ : E * (P * Q) = E := by
    have : P * Q = (yO * Q.det) • (1 : Matrix (Fin k) (Fin k) O) := by
      rw [hPdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    rw [this, hEdef, smul_mul_smul, one_mul]
    congr 1
    calc εO * (yO * Q.det) = wO * (eO * Q.det * yO) := by rw [hεdef]; ring
      _ = εO := by rw [hey, hεdef, mul_comm]
  refine ⟨E * Mo + (1 - E), E * (P * No) + (1 - E), ?_, ?_⟩
  · rw [mat_idem_mul E _ _ hE2 hEc]
    have : E * (P * No * Mo) = E := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEc P, Matrix.mul_assoc, hEQ, ← Matrix.mul_assoc, ← hEc P,
        Matrix.mul_assoc, hEPQ]
    rw [this, add_sub_cancel]
  · intro i j
    have hEC : E * (E * Mo + (1 - E)) = E * Mo := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, hE2, Matrix.mul_sub, Matrix.mul_one, hE2, sub_self, add_zero]
    have := congrFun (congrFun hEC i) j
    simpa [hEdef, Matrix.smul_mul] using this

theorem idxDMat_of (hJ : IdxDJacE) : IdxDMat := by
  intro D X TR e he A
  have heO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Set.mem_union_right _ ⟨⟨e, he.1⟩, rfl⟩)
  obtain ⟨t, ht, het⟩ := he.2.2.1
  have htO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)
  let eO : IntAf X.B.I.F X.B.I.E := ⟨_, heO⟩
  let wO : IntAf X.B.I.F X.B.I.E := ⟨X.ew, X.ew_int⟩
  let tO : IntAf X.B.I.F X.B.I.E := ⟨_, htO⟩
  let gO : IntAf X.B.I.F X.B.I.E := X.B.g
  have hgO : ((gO : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    simp [gO]
  have kerZ : ∀ x : IntAf X.B.I.F X.B.I.E, (∀ v, TR.res v x = 0) →
      ∃ t : IntAf X.B.I.F X.B.I.E, wO * x = gO * t := by
    intro x hx
    obtain ⟨t, ht, he'⟩ := (TR.res_ker x).1 hx
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    change X.ew * (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t
    rw [hgO]; exact he'
  have resG : ∀ v, TR.res v gO = 0 := by
    refine (TR.res_ker gO).2 ⟨X.ew, X.ew_int, ?_⟩
    rw [hgO, mul_comm]
  have heq : eO = 1 - gO * tO := by
    apply Subtype.ext
    change (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e = 1 - (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t)
    rw [hgO]
    have h1 : e = 1 - (X.B.g : Af X.B.I.F) * t := by rw [← het]; ring
    rw [h1, TensorProduct.tmul_sub]
    congr 1
    rw [← map_natCast (Algebra.TensorProduct.includeRight (R := X.B.I.F) (A := X.B.I.E) (B := Af X.B.I.F)) X.B.g]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have resE : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * x) = TR.res v x := by
    intro v x
    rw [heq, sub_mul, one_mul, map_sub, mul_assoc, map_mul, resG, zero_mul, sub_zero]
  have resEps : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * wO * x) = TR.res v x := by
    intro v x
    rw [mul_assoc, resE]
    exact TR.res_ew v x
  choose a0 ha0 using fun i j => TR.res_joint (fun v => (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
  choose b0 hb0 using fun i j => TR.res_joint
    (fun v => ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) i j)
  let Mo : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E) := Matrix.of a0
  let No : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E) := Matrix.of b0
  have hNM : ∀ v i j, TR.res v ((No * Mo - 1) i j) = 0 := by
    intro v i j
    have hM : (TR.res v).mapMatrix Mo = (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := by
      ext i j; exact congrFun (ha0 i j) v
    have hN : (TR.res v).mapMatrix No = ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) := by
      ext i j; exact congrFun (hb0 i j) v
    have : (TR.res v).mapMatrix (No * Mo - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one, sub_self]
    exact congrFun (congrFun this i) j
  choose tt htt using fun i j => kerZ _ (fun v => hNM v i j)
  have hw2 : wO * wO = wO := Subtype.ext X.ew_idem
  have he2 : eO * eO = eO := Subtype.ext (by
    change ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, he.2.1])
  have hJO : ∀ m : IntAf X.B.I.F X.B.I.E, ∃ y : IntAf X.B.I.F X.B.I.E, eO * (1 + gO * m) * y = eO := by
    intro m
    obtain ⟨y, hy, hyeq⟩ := hJ X.B.I.F X.B.I.E X.B.g e he (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) m.2
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * (1 + (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m) * y =
      (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e
    rw [hgO]; exact hyeq
  obtain ⟨CO, C'O, hCC, hent⟩ := mat_lift_core gO eO wO he2 hw2 Mo No (Matrix.of tt) (fun i j => htt i j) hJO
  refine ⟨CO.map (IntAf X.B.I.F X.B.I.E).subtype, C'O.map (IntAf X.B.I.F X.B.I.E).subtype, ?_,
    fun i j => ⟨(CO i j).2, (C'O i j).2⟩, ?_⟩
  · rw [← Matrix.map_mul, hCC, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro v i j
    have hmem : epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j ∈ IntAf X.B.I.F X.B.I.E :=
      (eO * wO * CO i j).2
    unfold resT
    rw [dite_eq_left hmem]
    have : (⟨epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j, hmem⟩ : IntAf X.B.I.F X.B.I.E) =
        eO * wO * Mo i j := by
      rw [← hent i j]; rfl
    rw [this, resEps]
    exact congrFun (ha0 i j) v

end PI.UnitaryDimensionFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKHom
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cj_good {D : D7} {X : HidaSetting D} (u : D.what₂.Word) (s : Hfin X u) (hs : cj X u s ∈ X.B.I.Kset) :
    NormCutK.Good X (cj X u s) := by
  have hk1 : (((1 : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ * ((s : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset := by
    simpa [cj, mul_assoc] using hs
  have hk2 : ((s : X.B.I.Gf) * X.xu u)⁻¹ * (((1 : Hfin X u) : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset := by
    have hi := PI.UnitaryDimensionFormula.kset_inv hs
    simpa [cj, mul_assoc, mul_inv_rev] using hi
  have hg := NormCutK.colGood X u 1 s hk1 hk2
  simpa [cj, mul_assoc] using hg

theorem idxHom : IdxHom := by
  intro D X Y u _
  refine ⟨NormCutK.levi_one (TR := Y.TR), fun s t hs ht => ?_, fun s hs hKu v => ?_⟩
  · have hst : cj X u (s * t) = cj X u s * cj X u t := by
      simp [cj, mul_assoc]
    rw [hst, NormCutK.levi_mul (TR := Y.TR) (cj_good u s hs) (cj_good u t ht)]
  · exact NormCutK.unitriangular_reduction_of_mem_level (TR := Y.TR) (cj_good u s hs) hKu v

end PI.UnitaryDimensionFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKLevi
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section AlgL

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

theorem hrow_dot (x y : Fin n → A) : hrow σ J x ⬝ᵥ y = Formalism.UG.hform σ J x y := by
  simp only [dotProduct, hrow, Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm

private lemma vecMulVec_mulVec_rank_two_dimension_formula (u v y : Fin n → A) : Matrix.vecMulVec u v *ᵥ y = (v ⬝ᵥ y) • u := by
  ext q
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

theorem sMat_mulVec (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) (y : Fin n → A) :
    sMat σ J b bs C D *ᵥ y = y + ∑ i, ∑ j, (((C - 1) i j * Formalism.UG.hform σ J (bs j) y) • b i +
      ((D - 1) i j * Formalism.UG.hform σ J (b j) y) • bs i) := by
  rw [sMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec_rank_two_dimension_formula,
    vecMulVec_mulVec_rank_two_dimension_formula, hrow_dot, hrow_dot, smul_smul, smul_smul]

end AlgL

section Main

variable {D : D7} {X : HidaSetting D}

theorem tmul_one_mem {e : Af X.B.I.F} (he : e ∈ Formalism.UG.intAd X.B.I.F) :
    ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.subset_closure (Or.inr ⟨⟨e, he⟩, rfl⟩)

theorem resT_congr (TR : TypedRed X) (v : TR.Pl) {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hy : y ∈ IntAf X.B.I.F X.B.I.E) (hZ : ZMod' X.B.I X.B.g (x - y)) : resT TR v x = resT TR v y := by
  obtain ⟨t, ht, hxy⟩ := hZ
  have hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E :=
    natCast_mem _ _
  have hgt : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t ∈ IntAf X.B.I.F X.B.I.E :=
    (IntAf X.B.I.F X.B.I.E).mul_mem hg ht
  have hx : x = y + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := sub_eq_iff_eq_add'.1 hxy
  have hxm : x ∈ IntAf X.B.I.F X.B.I.E := hx ▸ (IntAf X.B.I.F X.B.I.E).add_mem hy hgt
  have h0 : TR.res v ⟨_, hgt⟩ = 0 := by
    refine (TR.res_ker ⟨_, hgt⟩).2 ?_ v
    exact ⟨X.ew * t, (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int ht, mul_left_comm _ _ _⟩
  have hsplit : (⟨x, hxm⟩ : IntAf X.B.I.F X.B.I.E) = ⟨y, hy⟩ + ⟨_, hgt⟩ := Subtype.ext hx
  simp only [resT, dif_pos hxm, dif_pos hy]
  rw [hsplit, map_add (TR.res v), h0, add_zero]

theorem idxDLevi : IdxDLevi := by
  intro D X TR e he b bs hF hL hC C C' _ hCint v i j
  have hew := X.ew_int
  have hbwd : ∀ l, X.bwd l ∈ X.B.I.Lf := fun l => (X.vectorsInLattice.2.2 l).2
  have he1 : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E := tmul_one_mem he.1
  have hεint : epsX X e * C i j ∈ IntAf X.B.I.F X.B.I.E := mul_mem (mul_mem he1 hew) (hCint i j).1
  apply resT_congr TR v hεint
  have hh : ∀ x y : VA X.B.I, Formalism.UG.hform (sigA X.B.I) (JA X.B.I) x y = hA X.B.I x y := fun _ _ => rfl
  have hsig1 : sigA X.B.I ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e := by
    rw [unitaryCongruence.sigA_tmul, star_one]
  have hzero : ∀ q, hA X.B.I (b q) (X.bw j) = 0 := by
    intro q
    rw [hF.2.2.1 q, X.bw_w j, unitaryCongruence.hA_smul_left, unitaryCongruence.hA_smul_right]
    unfold epsX
    rw [map_mul, hsig1]
    have := X.ew_orth
    linear_combination ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * hA X.B.I (b q) (X.bw j) * this
  have hexp : hA X.B.I (X.bwd i) (sMat (sigA X.B.I) (JA X.B.I) b bs C (C'.map (sigA X.B.I))ᵀ *ᵥ X.bw j) =
      hA X.B.I (X.bwd i) (X.bw j) +
        ∑ p, ∑ q, (C - 1) p q * hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) := by
    rw [sMat_mulVec]
    simp only [hh]
    rw [← unitaryCongruence.hL_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, unitaryCongruence.hL_apply, smul_eq_mul, hzero, mul_zero, zero_mul,
      add_zero]
  rw [hexp]
  have hCm : ∀ p q, (C - 1) p q ∈ IntAf X.B.I.F X.B.I.E := by
    intro p q
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine sub_mem (hCint p q).1 ?_
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  set S1 := ∑ p, ∑ q, (C - 1) p q * hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) with hS1
  set S2 := ∑ p, ∑ q, (C - 1) p q * ((if q = j then X.ew else 0) * (if i = p then X.ew else 0)) with hS2
  have key1 : ZMod' X.B.I X.B.g (S1 - S2) := by
    have eq : S1 - S2 = ∑ p, ∑ q, (C - 1) p q * (hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) -
        (if q = j then X.ew else 0) * (if i = p then X.ew else 0)) := by
      rw [hS1, hS2]
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [eq]
    refine unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun p _ => unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun q _ => ?_
    refine unitaryCongruence.Z_smul X.B.I X.B.g (hCm p q) ?_
    have eq2 : hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) -
        (if q = j then X.ew else 0) * (if i = p then X.ew else 0) =
        hA X.B.I (X.bwd i) (b p) * (hA X.B.I (bs q) (X.bw j) - if q = j then X.ew else 0) +
        (if q = j then X.ew else 0) * (hA X.B.I (X.bwd i) (b p) - if i = p then X.ew else 0) := by ring
    rw [eq2]
    refine unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_smul X.B.I X.B.g
      (unitaryCongruence.hA_int X.B.I (hbwd i) (hL p).1) (hC q j).1) (unitaryCongruence.Z_smul X.B.I X.B.g ?_ (hC i p).2)
    split_ifs
    · exact hew
    · exact zero_mem _
  have hsum : S2 = (C - 1) i j * X.ew := by
    rw [hS2]
    simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', X.ew_idem]
  obtain ⟨t, ht, het⟩ := he.2.2.1
  have hlast : ZMod' X.B.I X.B.g ((if i = j then X.ew else 0) + (C - 1) i j * X.ew - epsX X e * C i j) := by
    refine ⟨((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) * X.ew * C i j,
      mul_mem (mul_mem (tmul_one_mem ht) hew) (hCint i j).1, ?_⟩
    have hg : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] ((X.B.g : Af X.B.I.F)) = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      rw [← Algebra.TensorProduct.includeRight_apply (R := X.B.I.F) (A := X.B.I.E), map_natCast]
    have h1 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 - e) =
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) := by
      rw [het, ← hg, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 - e) = 1 - (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e := by
      rw [TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]
    have h3 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e =
        1 - (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) := by
      rw [← h1, h2]; ring
    unfold epsX
    rw [Matrix.sub_apply, Matrix.one_apply, h3]
    split_ifs <;> ring
  have eqF : hA X.B.I (X.bwd i) (X.bw j) + S1 - epsX X e * C i j =
      (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (S1 - S2) + (S2 - (C - 1) i j * X.ew) +
        ((if i = j then X.ew else 0) + (C - 1) i j * X.ew - epsX X e * C i j) := by ring
  have h0 : S2 - (C - 1) i j * X.ew = 0 := by rw [hsum, sub_self]
  rw [eqF, h0, add_zero]
  exact unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_add X.B.I X.B.g (X.bw_dual i j) key1) hlast

end Main

end PI.UnitaryDimensionFormula
end
end

