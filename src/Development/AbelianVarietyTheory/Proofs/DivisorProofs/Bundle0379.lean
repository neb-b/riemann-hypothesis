module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0346
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLog
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
open scoped MvPowerSeries.WithPiTopology

namespace GlobalTheory.LogJacobian

noncomputable section

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def substSecondBlockZero (d : ℕ) : Fin d ⊕ Fin d → MvPowerSeries (Fin d) C :=
  Sum.elim (fun b => X b) (fun _ => 0)

theorem constantCoeff_substSecondBlockZero (d : ℕ) (s : Fin d ⊕ Fin d) : constantCoeff (substSecondBlockZero (C := C) d s) = 0 := by
  cases s <;> simp [substSecondBlockZero]

theorem hasSubst_substSecondBlockZero (d : ℕ) : HasSubst (substSecondBlockZero (C := C) d) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_substSecondBlockZero d)

def jacEntry (G : LogFGL v d) (k l : Fin d) : MvPowerSeries (Fin d) C :=
  subst (substSecondBlockZero d) (pderiv (Sum.inr k) (G.F l))

theorem natCast_int (n : ℕ) : IsIntV v (n : C) := by
  induction n with
  | zero => simp [IsIntV]
  | succ n ih =>
    unfold IsIntV at *
    push_cast
    exact le_trans (le_min ih (by rw [v.map_one])) (v.map_add _ _)

theorem mvIsInt_pderiv {σ : Type} {f : MvPowerSeries σ C} (hf : MvIsInt v f) (i : σ) :
    MvIsInt v (pderiv i f) := by
  intro n
  unfold IsIntV
  rw [coeff_pderiv, v.map_mul]
  have h2 : ((n i : C) + 1) = ((n i + 1 : ℕ) : C) := by push_cast; ring
  rw [h2]
  exact add_nonneg (hf _) (natCast_int _)

theorem mvIsInt_substSecondBlockZero (d : ℕ) (s : Fin d ⊕ Fin d) : MvIsInt v (substSecondBlockZero (C := C) d s) := by
  intro n
  unfold IsIntV
  cases s with
  | inl b => simp only [substSecondBlockZero, Sum.elim_inl]; rw [coeff_X]; split_ifs <;> simp
  | inr b => simp [substSecondBlockZero]

theorem jacEntry_int (G : LogFGL v d) (k l : Fin d) : MvIsInt v (jacEntry G k l) :=
  ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (mvIsInt_pderiv (G.F_int l) _) (mvIsInt_substSecondBlockZero d) (constantCoeff_substSecondBlockZero d)

theorem subst_zero_eq (g : MvPowerSeries (Fin d) C) :
    subst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) C)) g = MvPowerSeries.C (constantCoeff g) := by
  have : (fun _ : Fin d => (0 : MvPowerSeries (Fin d) C)) = ((0 : Fin d → C) • X) := by
    funext i; simp
  rw [this, ← rescale_eq_subst, rescale_zero_apply]

theorem subst_substSecondBlockZero_firstBlock_log (G : LogFGL v d) (a : Fin d) :
    subst (substSecondBlockZero (C := C) d) (subst (fun b => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) (G.lg a))
      = G.lg a := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (fun b => constantCoeff_X _)) (hasSubst_substSecondBlockZero d)]
  have : (fun b : Fin d => subst (substSecondBlockZero (C := C) d) (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C))
      = fun b => X b := by
    funext b; rw [subst_X (hasSubst_substSecondBlockZero d)]; rfl
  rw [this, subst_self]; rfl

theorem subst_substSecondBlockZero_secondBlock (G : LogFGL v d) (g : MvPowerSeries (Fin d) C) :
    subst (substSecondBlockZero (C := C) d) (subst (fun b => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) g)
      = MvPowerSeries.C (constantCoeff g) := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (fun b => constantCoeff_X _)) (hasSubst_substSecondBlockZero d)]
  have : (fun b : Fin d => subst (substSecondBlockZero (C := C) d) (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C))
      = fun _ => 0 := by
    funext b; rw [subst_X (hasSubst_substSecondBlockZero d)]; rfl
  rw [this, subst_zero_eq]

theorem formalGroupLaw_subst_secondBlock_zero (G : LogFGL v d) (l : Fin d) : subst (substSecondBlockZero (C := C) d) (G.F l) = (X l : MvPowerSeries (Fin d) C) := by
  obtain ⟨⟨hE0, hlgE⟩, hElg, -⟩ := _root_.GlobalTheory.FGDepth.expOf_twoSided_unique C v d G
  have hF0c : ∀ l, constantCoeff (subst (substSecondBlockZero (C := C) d) (G.F l)) = 0 := fun l =>
    constantCoeff_subst_eq_zero (hasSubst_substSecondBlockZero d) (constantCoeff_substSecondBlockZero d) (G.F_const l)
  have hF0 : HasSubst (fun l => subst (substSecondBlockZero (C := C) d) (G.F l)) := hasSubst_of_constantCoeff_zero hF0c
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have key : ∀ a, subst (fun l => subst (substSecondBlockZero (C := C) d) (G.F l)) (G.lg a) = G.lg a := by
    intro a
    rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) (hasSubst_substSecondBlockZero d), G.lg_F a,
      subst_add (hasSubst_substSecondBlockZero d), subst_substSecondBlockZero_firstBlock_log, subst_substSecondBlockZero_secondBlock G, G.lg_const a, map_zero, add_zero]
  have e1 : subst (fun l => subst (substSecondBlockZero (C := C) d) (G.F l)) (X l : MvPowerSeries (Fin d) C)
      = subst (substSecondBlockZero d) (G.F l) := subst_X hF0 l
  rw [← e1, ← hElg l, subst_comp_subst_apply hlg hF0]
  simp only [key, hElg]

-- Inline the chain rule in the proofs that differentiate a substitution.
local macro "have_subst_chain_rule " h:ident : tactic => `(tactic|
  have $h {R σ τ : Type} [CommRing R] [Fintype σ] {a : σ → MvPowerSeries τ R}
      (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) (j : τ) :
      pderiv j (subst a f) = ∑ i, subst a (pderiv i f) * pderiv j (a i) := by
    classical
    let : UniformSpace R := ⊥
    have ha := hasSubst_of_constantCoeff_zero ha0
    have hc := continuous_subst (R := R) ha
    have hs0 : subst a (0 : MvPowerSeries σ R) = 0 := by rw [← coe_substAlgHom ha, map_zero]
    have hs1 : subst a (1 : MvPowerSeries σ R) = 1 := by rw [← coe_substAlgHom ha, map_one]
    have hd {ι : Type} (i : ι) :
        Continuous (pderiv (R := R) i : MvPowerSeries ι R → MvPowerSeries ι R) := by
      apply continuous_pi
      intro n
      change Continuous (fun g : MvPowerSeries ι R => coeff n (pderiv i g))
      simp only [coeff_pderiv]
      exact (MvPowerSeries.WithPiTopology.continuous_coeff R (n + Finsupp.single i 1)).mul
        continuous_const
    refine congr_fun (DenseRange.equalizer
      (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries (σ := σ) (R := R))
      (g := fun f => pderiv j (subst a f))
      (h := fun f => ∑ i, subst a (pderiv i f) * pderiv j (a i))
      ((hd j).comp hc)
      (continuous_finsetSum _ fun i _ => (hc.comp (hd i)).mul continuous_const) ?_) f
    funext p
    simp only [Function.comp_apply]
    induction p using MvPolynomial.induction_on with
    | C r =>
      simp only [MvPolynomial.coe_C, subst_C, pderiv_C, hs0, zero_mul, Finset.sum_const_zero]
    | add p q hp hq =>
      simp only [MvPolynomial.coe_add, subst_add ha, map_add (f := _), hp, hq,
        add_mul, Finset.sum_add_distrib]
    | mul_X p i hp =>
      simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, Derivation.leibniz, hp,
        smul_eq_mul, subst_add ha, subst_X ha, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · rw [Finset.sum_eq_single i]
        · simp only [pderiv_X_self, hs1, mul_one]
        · intro b _ hb
          simp only [pderiv_X_of_ne (Ne.symm hb), hs0, mul_zero, zero_mul]
        · simp
      · exact Finset.sum_congr rfl fun i _ => by ring)

theorem jac_lg_mul_jacEntry (G : LogFGL v d) (a k : Fin d) :
    ∑ l, pderiv l (G.lg a) * jacEntry G k l = if a = k then 1 else 0 := by
  classical
  have_subst_chain_rule hchain
  have h := congrArg (pderiv (Sum.inr k)) (G.lg_F a)
  rw [hchain G.F_const, map_add (f := _), hchain (fun b => constantCoeff_X _),
    hchain (fun b => constantCoeff_X _)] at h
  simp only [pderiv_X, Pi.single_apply, reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero,
    zero_add, Sum.inr.injEq, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  have h2 := congrArg (subst (substSecondBlockZero (C := C) d)) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [subst_substSecondBlockZero_secondBlock G, ← coe_substAlgHom (hasSubst_substSecondBlockZero d), map_sum] at h2
  simp only [map_mul, coe_substAlgHom] at h2
  simp only [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) (hasSubst_substSecondBlockZero d), formalGroupLaw_subst_secondBlock_zero,
    subst_self, id] at h2
  have hc : constantCoeff (pderiv k (G.lg a)) = if a = k then 1 else 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, G.lg_lin]; simp
  simp only [jacEntry]
  rw [h2, hc]
  split_ifs <;> simp

theorem pderiv_expOf (G : LogFGL v d) (l k : Fin d) :
    pderiv k (expOf G l) = subst (expOf G) (jacEntry G k l) := by
  classical
  have_subst_chain_rule hchain
  obtain ⟨⟨hE0, hlgE⟩, -, -⟩ := _root_.GlobalTheory.FGDepth.expOf_twoSided_unique C v d G
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  let J : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) C) :=
    Matrix.of fun a l => subst (expOf G) (pderiv l (G.lg a))
  let M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) C) :=
    Matrix.of fun l k => pderiv k (expOf G l)
  let N : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) C) :=
    Matrix.of fun l k => subst (expOf G) (jacEntry G k l)
  have hJM : J * M = 1 := by
    ext a k
    have h := congrArg (pderiv k) (hlgE a)
    rw [hchain hE0, pderiv_X, Pi.single_apply] at h
    simp only [J, M, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, h]
  have hJN : J * N = 1 := by
    refine Matrix.ext fun a k => ?_
    have h := congrArg (subst (expOf G)) (jac_lg_mul_jacEntry G a k)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← coe_substAlgHom hE, map_sum] at h
    simp only [map_mul, coe_substAlgHom] at h
    simp only [J, N, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, h]
    split_ifs
    · rw [← substAlgHom_apply hE, map_one]
    · rw [← substAlgHom_apply hE, map_zero]
  have hNJ : N * J = 1 := mul_eq_one_comm.mp hJN
  have hMN : M = N := by
    calc M = (N * J) * M := by rw [hNJ, Matrix.one_mul]
      _ = N * (J * M) := Matrix.mul_assoc _ _ _
      _ = N := by rw [hJM, Matrix.mul_one]
  exact congrFun (congrFun hMN l) k

theorem exists_integral_invariant_derivation : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d), ∃ D : Fin d → Fin d → MvPowerSeries (Fin d) C, (∀ k l, MvIsInt v (D k l)) ∧ ∀ (f : MvPowerSeries (Fin d) C) (k : Fin d) (α : Fin d →₀ ℕ), ((α k : C) + 1) * coeff (α + Finsupp.single k 1) (subst (expOf G) f) = coeff α (subst (expOf G) (∑ l, D k l * (show MvPowerSeries (Fin d) C from fun β => ((β l : C) + 1) * coeff (β + Finsupp.single l 1) f))) := by
  intro C _ _ v d G
  have_subst_chain_rule hchain
  refine ⟨jacEntry G, jacEntry_int G, fun f k α => ?_⟩
  obtain ⟨⟨hE0, -⟩, -, -⟩ := _root_.GlobalTheory.FGDepth.expOf_twoSided_unique C v d G
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  have hP : ∀ l, (show MvPowerSeries (Fin d) C from
      fun β => ((β l : C) + 1) * coeff (β + Finsupp.single l 1) f) = pderiv l f := by
    intro l; ext β; rw [coeff_pderiv, mul_comm]; rfl
  simp only [hP]
  rw [mul_comm, ← coeff_pderiv, hchain hE0]
  simp only [pderiv_expOf]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← substAlgHom_apply hE, map_sum]
  simp only [map_mul, substAlgHom_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end

end GlobalTheory.LogJacobian
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseUnipotentVolumeConjDiagonalEq
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.DiagVol

section Main
variable {K₀ : Type} [Field K₀] {ι : Type} [Fintype ι] [DecidableEq ι]

def unipSub (ℓ : ι → ℕ) : Subgroup (GL ι K₀) where
  carrier := {g | ∀ r s, ℓ s ≤ ℓ r → g.val r s = (1 : Matrix ι ι K₀) r s}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {a b} ha hb r s hrs => by
    have tri : b.val.BlockTriangular ℓ := fun i j h => by
      rw [hb i j h.le, Matrix.one_apply_ne]; rintro rfl; exact lt_irrefl _ h
    have : (a.val * b.val) r s = ((1 : Matrix ι ι K₀) * b.val) r s := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : ℓ u ≤ ℓ r
      · rw [ha r u hu]
      · rw [tri (show ℓ s < ℓ u by omega)]; simp
    rw [Units.val_mul, this, Matrix.one_mul, hb r s hrs]
  inv_mem' := fun {a} ha r s hrs => by
    have tri : (a⁻¹).val.BlockTriangular ℓ := by
      rw [Matrix.coe_units_inv]
      haveI := a.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular fun i j h => by
        rw [ha i j h.le, Matrix.one_apply_ne]; rintro rfl; exact lt_irrefl _ h
    have : (a.val * (a⁻¹).val) r s = ((1 : Matrix ι ι K₀) * (a⁻¹).val) r s := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : ℓ u ≤ ℓ r
      · rw [ha r u hu]
      · rw [tri (show ℓ s < ℓ u by omega)]; simp
    rw [Units.mul_inv, Matrix.one_mul] at this
    exact this.symm
end Main

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem symN_le_unipSub {F : Type} [Field F] : symN F n c ≤ unipSub (ordL c) := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_) <;> rw [Model.mem_N_iff] at hx <;>
    intro r s hrs <;> refine hx r s ?_ <;>
    rcases r with r | r <;> rcases s with s | s <;> simp only [ordL, lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega

theorem conj_diag_mem {F : Type} [Field F] (d : n ⊕ Fin c → Fˣ) {x : GL (n ⊕ Fin c) F} (hx : x ∈ symN F n c) :
    diagGL d * x * (diagGL d)⁻¹ ∈ symN F n c := by
  have key : ∀ p, ∀ y ∈ N F n c p, diagGL d * y * (diagGL d)⁻¹ ∈ N F n c p := by
    intro p y hy
    rw [Model.mem_N_iff] at hy ⊢
    intro r s h
    have e : ((diagGL d)⁻¹).val = Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F) := rfl
    rw [Units.val_mul, Units.val_mul, e, diagGL_val, Matrix.mul_diagonal, Matrix.diagonal_mul, hy r s h]
    by_cases hrs : r = s
    · subst hrs; simp
    · simp [Matrix.one_apply_ne hrs]
  have h : symN F n c ≤ (symN F n c).comap (MulAut.conj (diagGL d)).toMonoidHom :=
    sup_le (fun v hv => Subgroup.mem_sup_left (by simpa using key _ v hv))
      fun v hv => Subgroup.mem_sup_right (by simpa using key _ v hv)
  simpa using h hx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem invVol_diag_one (ϖ : kˣ) (hϖ : IsUnif ϖ) (t : n ⊕ Fin c) :
    ∃ z : ℤ, invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom) =
      (resCard k : ℚ) ^ z ∧ |z| ≤ Fintype.card (n ⊕ Fin c) := by
  set g := diagGL (Pi.mulSingle t ϖ) with hg
  set K := KO k (n ⊕ Fin c)
  set C := K.map (MulAut.conj g).toMonoidHom with hC
  set Sout := Finset.univ.filter (fun s : n ⊕ Fin c => ordL c t < ordL c s)
  set Sin := Finset.univ.filter (fun r : n ⊕ Fin c => ordL c r < ordL c t)
  have hU : ∀ x ∈ symN k n c ⊓ K, ∀ r s, ordL c s ≤ ordL c r → x.val r s = (1 : Matrix _ _ k) r s :=
    fun x hx => symN_le_unipSub (Subgroup.mem_inf.1 hx).1

  have hnum : C.relIndex (symN k n c ⊓ K) = resCard k ^ Sout.card := by
    refine _root_.GlobalTheory.DiagVol.RowIdx.relIndex_rowCong ϖ hϖ t Sout (by simp [Sout]) _ inf_le_right (fun x hx s hs => ?_) (fun y hy h0 => ?_)
    · exact hU x hx t s (by simpa [Sout] using hs)
    · exact _root_.GlobalTheory.DiagVol.rowElt_mem t y hy fun s hs => h0 s (by simpa [Sout] using hs)

  have hden : K.relIndex (symN k n c ⊓ C) = resCard k ^ Sin.card := by
    set φ := (MulAut.conj g⁻¹).toMonoidHom
    have hφ : Function.Injective φ := (MulAut.conj g⁻¹).injective
    have hCφ : C.map φ = K := by
      rw [hC, Subgroup.map_map]
      conv_rhs => rw [← Subgroup.map_id K]
      congr 1
      ext x; simp [φ, mul_assoc]
    have hNφ : (symN k n c).map φ = symN k n c := by
      have hgi : g⁻¹ = diagGL (Pi.mulSingle t ϖ)⁻¹ := Units.ext rfl
      refine le_antisymm ?_ fun x hx => ?_
      · rintro _ ⟨x, hx, rfl⟩
        simpa [φ, hgi] using conj_diag_mem (Pi.mulSingle t ϖ)⁻¹ hx
      · refine ⟨g * x * g⁻¹, conj_diag_mem _ hx, ?_⟩
        simp [φ, mul_assoc]
    rw [← Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.map_inf_eq _ _ _ hφ, hNφ, hCφ]
    refine _root_.GlobalTheory.IndexCol.relIndex_conj_col ϖ hϖ t Sin (by simp [Sin]) _ inf_le_right (fun x hx r hr => ?_) (fun y hy h0 => ?_)
    · exact hU x hx r t (by simpa [Sin] using hr)
    · exact GlobalTheory.T.flagColumnUnipotent_mem_periodUnipotent_integralGL t y hy fun r hr => h0 r (by simpa [Sin] using hr)
  have hq : (0 : ℚ) < resCard k := by
    have : 1 < resCard k := Finite.one_lt_card
    exact_mod_cast this.trans' one_pos
  refine ⟨(Sout.card : ℤ) - Sin.card, ?_, ?_⟩
  · rw [invVol, hnum, hden, zpow_sub₀ hq.ne']
    push_cast; rfl
  · have h1 : Sout.card ≤ Fintype.card (n ⊕ Fin c) := Finset.card_le_univ _
    have h2 : Sin.card ≤ Fintype.card (n ⊕ Fin c) := Finset.card_le_univ _
    rw [abs_le]; constructor <;> omega

end GlobalTheory.DiagVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariant
section
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
private theorem exists_mulBy_pow_eq_comp_resOne' {p : ℕ} {R : Type} [CommRing R]
    (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ) :
    ∃ M : G.A 1 →ₐc[R] G.A (n + 1),
      ∀ a : G.A (n + 1),
        _root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n) a = M (G.resOne n a) := by
  induction n with
  | zero =>
    refine ⟨BialgHom.id R (G.A 1), fun a => ?_⟩
    have h := _root_.GlobalTheory.PDiv.mulBy_comp (BialgHom.id R (G.A 1)) 1
    rw [pow_one, toConv_ofConv] at h
    rw [_root_.GlobalTheory.PDivGroup.resOne_zero]
    simpa using congrArg (fun f : G.A 1 →ₐc[R] G.A 1 => f a) h
  | succ n ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨(G.mulP (n + 1)).comp M, fun a => ?_⟩
    rw [pow_succ, ← _root_.GlobalTheory.PDiv.mulBy_mulBy, ← _root_.GlobalTheory.PDivGroup.mulP_res,
      ← _root_.GlobalTheory.PDiv.map_mulBy, hM, _root_.GlobalTheory.PDivGroup.resOne_succ, BialgHom.comp_apply]


set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
    (n : ℕ) (a : G.A (n + 1))
    (ha : G.transl n a = a ⊗ₜ[R] 1) :
    ∃ e : G.A n, G.mulP n e = a := by
  obtain ⟨M, hM⟩ := exists_mulBy_pow_eq_comp_resOne' G n
  have key : ∀ χ φ : _root_.GlobalTheory.CartierDual R (G.A (n + 1)),
      (χ * _root_.GlobalTheory.CartierDual.map
        (_root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n)) φ).ofConv a =
        χ.ofConv a * φ.ofConv 1 := by
    intro χ φ
    have h1 : (_root_.GlobalTheory.CartierDual.map
        (_root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n)) φ).ofConv =
        (φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1))) ∘ₗ
          (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1) := by
      ext x
      simp [_root_.GlobalTheory.CartierDual.map_apply, hM]
    rw [_root_.GlobalTheory.CartierDual.mul_apply, _root_.GlobalTheory.CartierDual.pair_tmul, h1]
    have h2 : ∀ t, TensorProduct.map χ.ofConv
        ((φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1))) ∘ₗ
          (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1)) t =
        TensorProduct.map χ.ofConv
          (φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1)))
          (LinearMap.lTensor _
            (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1) t) := by
      intro t
      rw [LinearMap.lTensor, ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]
    rw [h2, ← _root_.GlobalTheory.PDivGroup.transl_apply, ha]
    simp
  let K : Ideal (_root_.GlobalTheory.CartierDual R (G.A (n + 1))) :=
    { carrier := {ψ | ∀ χ : _root_.GlobalTheory.CartierDual R (G.A (n + 1)), (χ * ψ).ofConv a = 0}
      add_mem' := by
        intro x y hx hy χ
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [mul_add, ofConv_add, LinearMap.add_apply, hx, hy, add_zero]
      zero_mem' := by
        intro χ
        simp
      smul_mem' := by
        intro c x hx χ
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [← mul_assoc]
        exact hx _ }
  have hK : _root_.GlobalTheory.PDiv.torsionIdeal (R := R) (A := _root_.GlobalTheory.CartierDual R (G.A (n + 1))) (p ^ n) ≤
      RingHom.ker (Ideal.Quotient.mkₐ R K) := by
    change _root_.GlobalTheory.PDiv.kerIdeal (_root_.GlobalTheory.PDiv.mulBy R _ (p ^ n)) ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro φ hφ
    have hφ₀ : CoalgebraStruct.counit (R := R) φ = 0 := hφ
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Ideal.Quotient.mkₐ R K (_root_.GlobalTheory.PDiv.mulBy R _ (p ^ n) φ) = 0
    rw [← _root_.GlobalTheory.PDiv.dual_mulBy, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    intro χ
    rw [key, ← _root_.GlobalTheory.CartierDual.counit_apply, hφ₀, mul_zero]
  have hker : ∀ ψ, _root_.GlobalTheory.CartierDual.map (G.mulP n) ψ = 0 →
      ψ.ofConv a = 0 := by
    intro ψ hψ
    have h3 : ψ ∈ RingHom.ker (Ideal.Quotient.mkₐ R K) := by
      apply hK
      rw [← _root_.GlobalTheory.PDivGroup.ker_dual_mulP]
      exact hψ
    rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h3
    simpa using h3 1
  set πL : _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] _root_.GlobalTheory.CartierDual R (G.A n) :=
    (_root_.GlobalTheory.CartierDual.map (G.mulP n) :
      _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] _root_.GlobalTheory.CartierDual R (G.A n))
    with hπL
  have hs : Function.Surjective πL := _root_.GlobalTheory.PDivGroup.dual_mulP_surjective G n
  set evL : _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] R :=
    (_root_.GlobalTheory.CartierDual.cartierDualToBidual R (G.A (n + 1)) a).ofConv with hevL
  have hle : LinearMap.ker πL ≤ LinearMap.ker evL := by
    intro ψ hψ
    exact hker ψ hψ
  let L : _root_.GlobalTheory.CartierDual R (G.A n) →ₗ[R] R :=
    ((LinearMap.ker πL).liftQ evL hle).comp (πL.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hL : ∀ ψ, L (πL ψ) = ψ.ofConv a := by
    intro ψ
    have h4 : (πL.quotKerEquivOfSurjective hs).symm (πL ψ) = Submodule.Quotient.mk ψ := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, h4, Submodule.liftQ_apply]
    rfl
  obtain ⟨e, he⟩ :=
    (_root_.GlobalTheory.CartierDual.toBidual_bijective (R := R) (M := G.A n)).2 (toConv L)
  refine ⟨e, (_root_.GlobalTheory.CartierDual.toBidual_bijective (R := R) (M := G.A (n + 1))).1 ?_⟩
  apply WithConv.ext
  ext ψ
  show ψ.ofConv (G.mulP n e) = ψ.ofConv a
  rw [← _root_.GlobalTheory.CartierDual.map_apply]
  have h5 := congrArg
    (fun x => x.ofConv (_root_.GlobalTheory.CartierDual.map (G.mulP n) ψ)) he
  simp only [ofConv_toConv] at h5
  rw [← hL ψ]
  exact h5

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf : ∀ (R : Type) [CommRing R] , ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)), (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧ ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) = (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom := by
  first | (exact @GlobalTheory.EtC.chains_disc_homotopyEquiv) | (exact GlobalTheory.EtC.chains_disc_homotopyEquiv) | (intros; apply GlobalTheory.EtC.chains_disc_homotopyEquiv  <;> assumption)
end

