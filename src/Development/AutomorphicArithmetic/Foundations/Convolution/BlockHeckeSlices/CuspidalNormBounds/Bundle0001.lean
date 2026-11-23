module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapPoly
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CuspUmg
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

theorem UpperTheory.ConvolutionTheory.BW.cuspUmg :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CuspUmg E := by
  intro E _ _ _ n f hf
  refine ⟨⟨hf.1.isLeftInvariant, level_of hf.1.isSmooth hf.1.isKFinite, ?_⟩, hf.2⟩
  obtain ⟨C₀, N, hC₀⟩ := hf.1.hasModerateGrowth
  refine ⟨N, fun u => ?_⟩
  show HasGrowth (uC E n u f).1 N
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, fun g => by simp⟩
  | tmul c x =>
    obtain ⟨C, hC⟩ := hasGrowth_uAction x hf.1.isSmoothKZ ⟨C₀, hC₀⟩
    refine ⟨‖c‖ * C, fun g => ?_⟩
    rw [uC_tmul, mul_assoc]
    exact (norm_mul c _).le.trans (mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c))
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact hx.add hy
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.DatBasics
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup
open UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem posIdele_inf (s : ℝ) (hs : 0 < s) (w : InfinitePlace E) :
    ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ) := by
  have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  change GroundTheory.Global.posRealElem w _ = _
  unfold GroundTheory.Global.posRealElem
  rw [dite_eq_right hw]
  simp [InfinitePlace.mult, hw, Real.sqrt_sq hs.le]

private noncomputable def eU (E : Type) [Field E] (x : ℝ) : (Cinf E)ˣ where
  val := fun _ => (Real.exp x : ℂ)
  inv := fun _ => (Real.exp (-x) : ℂ)
  val_inv := funext fun _ => by simp [← Complex.exp_add]
  inv_val := funext fun _ => by simp [← Complex.exp_add]

private theorem diag_eq (a : Fin n → ℝ) :
    (diagUnits n fun i => posIdele (K := E) (Real.exp (a i)) (Real.exp_pos _) : GA E n) =
      infGL E n (diagUnits n fun i => eU E (a i)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  set y : GL (Fin n) (Cinf E) := diagUnits n fun i => eU E (a i) with hy
  have h2 : ((infGL E n y).val i j).2 = (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j :=
    congrArg (fun g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) => g.val i j) (pFin_infGL y)
  have h1 : ∀ w, ((infGL E n y).val i j).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val i j w) :=
    fun w => congrFun (infGL_entry y i j) w
  have hyv : y.val = Matrix.diagonal fun i => (fun _ : InfinitePlace E => (Real.exp (a i) : ℂ)) := rfl
  rw [coe_diagUnits]
  refine Prod.ext (funext fun w => ?_) ?_
  · rw [h1, hyv]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdele_inf]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
      exact (map_zero _).symm
  · rw [h2]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact FiniteAdeleRing.ext E fun v => posIdele_finite _ _ v
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rfl

private theorem sum_Eop (i : Fin n) : ∑ τ : E →+* ℂ, Eop τ i i = lie E n (toL (Matrix.single i i 1)) := by
  rw [lie_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ∀ k l, coord τ (toL (Matrix.single i i (1 : Cinf E)) k l) = if i = k then if i = l then 1 else 0 else 0 := by
    intro k l
    change coord τ (Matrix.single i i (1 : Cinf E) k l) = _
    rw [Matrix.single_apply]
    by_cases h1 : i = k <;> by_cases h2 : i = l <;> simp [h1, h2]
  simp only [e]
  simp

private theorem lie_one : lie E n (oneL E n) = ∑ τ : E →+* ℂ, ∑ i, Eop τ i i := by
  rw [lie_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ l, coord τ (oneL E n k l) = if k = l then 1 else 0 := by
    intro l
    change coord τ ((1 : Matrix (Fin n) (Fin n) (Cinf E)) k l) = _
    rw [Matrix.one_apply]
    split_ifs <;> simp
  simp only [e]
  simp

private theorem lie_one_eq_zero (hn : 0 < n) (f : Sm E n) (h : ∀ t g, f.1 (zt E n t * g) = f.1 g) :
    lie E n (oneL E n) f = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have hd : HasDerivAt (fun t : ℝ => toL (diagUnits n fun _ => eU E t : GL (Fin n) (Cinf E)).val) (oneL E n) 0 := by
    have e : (fun t : ℝ => toL (diagUnits n fun _ => eU E t : GL (Fin n) (Cinf E)).val) =
        fun t : ℝ => Real.exp t • oneL E n := by
      funext t k l w
      change (Matrix.diagonal fun _ => (fun _ : InfinitePlace E => (Real.exp t : ℂ))) k l w =
        Real.exp t • (1 : Matrix (Fin n) (Fin n) (Cinf E)) k l w
      by_cases h : k = l
      · subst h; simp
      · simp [h]
    rw [e]
    simpa using (Real.hasDerivAt_exp 0).smul_const (oneL E n)
  have h0 : (diagUnits n fun _ => eU E 0 : GL (Fin n) (Cinf E)) = 1 := by
    rw [← map_one (diagUnits n)]
    congr 1
    funext i
    exact Units.ext (funext fun _ => by simp [eU])
  have h1 := hasDerivAt_curve f g (fun t => diagUnits n fun _ => eU E t) _ h0 hd
  have e : (fun t : ℝ => f.1 (g * infGL E n (diagUnits n fun _ => eU E t))) = fun _ => f.1 g := by
    funext t
    have ha : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    have e : rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹ ⟨Real.exp (n * Module.finrank ℚ E * t), Real.exp_pos _⟩ =
        ⟨Real.exp t, Real.exp_pos t⟩ := by
      refine Subtype.ext ?_
      change Real.exp (n * Module.finrank ℚ E * t) ^ ((n * Module.finrank ℚ E : ℝ))⁻¹ = Real.exp t
      rw [← Real.exp_mul]
      congr 1
      field_simp
    rw [← h (n * Module.finrank ℚ E * t) g, ← diag_eq, zt, centralSection_mul_comm, centralSection, MonoidHom.comp_apply,
      MonoidHom.comp_apply, e]
    rfl
  rw [e] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem trace_eq {f : Sm E n} {τ : E →+* ℂ} {Λ : Fin n → ℂ} (hn : 0 < n)
    (h : ∀ u, cap τ u f = (∏ i, (u + Λ i)) • f) : (∑ i, Eop τ i i) f = (∑ i, Λ i) • f := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨p, -, -, h3, h4⟩ := exists_capPoly (Eop (a := m + 1) τ) (ℓ ∘ₗ LinearMap.applyₗ f)
  have e : p = Polynomial.C (ℓ f) * ∏ i, (Polynomial.X - Polynomial.C (-Λ i)) := by
    refine Polynomial.funext fun u => ?_
    rw [h4]
    change ℓ (cap τ u f) = _
    rw [h, map_smul]
    simp [Polynomial.eval_prod, mul_comm]
  have h5 := h3 m rfl
  have h6 := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (m + 1))) (fun i => -Λ i) (by simp)
  rw [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h6
  rw [e, Polynomial.coeff_C_mul, h6] at h5
  rw [map_sub, map_smul, sub_eq_zero]
  refine h5.symm.trans ?_
  simp [mul_comm]

private theorem blo_sum {S : Set (Pl E)} (b : Blo S n) : ∑ τ, ∑ i, b.Λ τ i = 0 := by
  have h := lie_one_eq_zero b.pos b.f b.cen
  rw [lie_one, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => trace_eq b.pos (b.inf τ), ← Finset.sum_smul] at h
  exact (smul_eq_zero.1 h).resolve_right b.ne

private theorem J_eq {S : Set (Pl E)} (d : Dat S n) (j : Fin d.len) : ∃ c : ℂ,
    d.J j = c • ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, lie E n (toL (Matrix.single i i 1)) :=
  ⟨_, by rw [Dat.J, Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop i]⟩

private theorem comm_lie (i l : Fin n) :
    Commute (lie E n (toL (Matrix.single i i 1))) (lie E n (toL (Matrix.single l l 1))) := by
  have h := isLieHom_ιC (E := E) (a := n) (Matrix.single i i 1) (Matrix.single l l 1)
  have e : Matrix.single i i (1 : Cinf E) * Matrix.single l l 1 - Matrix.single l l 1 * Matrix.single i i 1 = 0 := by
    by_cases h : i = l
    · subst h; simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h), sub_zero]
  rw [e] at h
  have h2 := congrArg (uC E n) h
  simp only [map_sub, map_mul, uC_ιC] at h2
  have z : lie E n (toL 0) = 0 := map_zero (lie E n)
  rw [z] at h2
  first | exact sub_eq_zero.1 h2 | exact sub_eq_zero.1 h2.symm

private theorem comm_rt (i : Fin n) (a : Fin n → (Cinf E)ˣ) :
    Commute (lie E n (toL (Matrix.single i i 1))) (rt E n (infGL E n (diagUnits n a))) := by
  have h := GlobalTheory.CapAdInv.rt_lie (E := E) (diagUnits n a) (Matrix.single i i 1)
  have e : (diagUnits n a).val * Matrix.single i i (1 : Cinf E) * ((diagUnits n a)⁻¹).val = Matrix.single i i 1 := by
    rw [Units.mul_inv_eq_iff_eq_mul, coe_diagUnits]
    ext k l
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp
  rw [e] at h
  exact h.symm

private theorem comb {S : Set (Pl E)} (d : Dat S n) : Function.Surjective d.idx ∧ d.len ≤ n ∧
    (∀ j, ∑ τ, ∑ i, (if d.idx i = j then d.lam τ i else 0) = 0) ∧
    ∀ j w, w ∉ S → (d.sat j w).card = ∑ i, if d.idx i = j then 1 else 0 := by
  induction d with
  | nil => exact ⟨fun j => j.elim0, le_rfl, fun j => j.elim0, fun j => j.elim0⟩
  | @cons r s b d ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    let I : Fin (r + s) → Fin (d.len + 1) := Fin.addCases (fun _ => 0) fun i => (d.idx i).succ
    refine ⟨?_, ?_, ?_, ?_⟩
    · change ∀ j : Fin (d.len + 1), ∃ i, I i = j
      refine Fin.cases ⟨Fin.castAdd s ⟨0, b.pos⟩, Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _⟩ fun j => ?_
      obtain ⟨i, rfl⟩ := h1 j
      exact ⟨Fin.natAdd r i, by simp [I]⟩
    · have := b.pos
      change d.len + 1 ≤ _
      omega
    · change ∀ j : Fin (d.len + 1), ∑ τ, ∑ i, (if I i = j then
        Fin.addCases (motive := fun _ => ℂ) (b.Λ τ) (d.lam τ) i else 0) = 0
      simp only [Fin.sum_univ_add, I, Fin.addCases_left, Fin.addCases_right]
      refine Fin.cases ?_ fun j => ?_
      · simpa [Fin.succ_ne_zero] using blo_sum b
      · simpa [(Fin.succ_ne_zero _).symm] using h3 j
    · change ∀ (j : Fin (d.len + 1)) w, w ∉ S →
        (Fin.cases (motive := fun _ => Pl E → Multiset ℂˣ) b.sat d.sat j w).card = ∑ i, if I i = j then 1 else 0
      simp only [Fin.sum_univ_add, I, Fin.addCases_left, Fin.addCases_right]
      refine Fin.cases (fun w hw => ?_) fun j w hw => ?_
      · simpa [Fin.succ_ne_zero] using (b.isSat w hw).2.2.1
      · simpa [(Fin.succ_ne_zero _).symm] using h4 j w hw

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.datBasics :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.DatBasics E := by
  intro E _ _ _
  refine ⟨fun S r b => blo_sum b, fun S n d => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := comb d
  have hp : ∀ x : ℝ, posIdele (K := E) (Real.exp x) (Real.exp_pos x) = posIdeleHom E ⟨Real.exp x, Real.exp_pos x⟩ :=
    fun _ => rfl
  refine ⟨h1, h2, fun j => ?_, fun j w hw => ?_, ?_, fun v v' => ?_, fun v => ⟨_, diag_eq _⟩, fun j l => ?_,
    fun j v => ?_, fun j => ?_⟩
  · rw [Finset.sum_filter, Fintype.sum_prod_type]
    exact h3 j
  · rw [h4 j w hw, Dat.size, Finset.card_filter]
  · rw [Dat.tr, ← map_one (diagUnits n)]
    congr 1
    funext i
    rw [hp, Pi.one_apply, ← map_one (posIdeleHom E)]
    congr 1
    exact Subtype.ext (by simp)
  · rw [Dat.tr, Dat.tr, Dat.tr, ← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, hp, hp, hp, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [add_div, Real.exp_add])
  · obtain ⟨c, hc⟩ := J_eq d j
    obtain ⟨c', hc'⟩ := J_eq d l
    rw [hc, hc']
    set_option synthInstance.maxHeartbeats 400000 in
    exact ((Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun k _ => comm_lie i k).smul_left c).smul_right c'
  · obtain ⟨c, hc⟩ := J_eq d j
    obtain ⟨a, ha⟩ : ∃ a : Fin n → (Cinf E)ˣ, d.tr v = infGL E n (diagUnits n a) := ⟨_, diag_eq _⟩
    rw [hc, ha]
    exact (Commute.sum_left _ _ _ fun i _ => comm_rt i a).smul_left c
  · obtain ⟨c, hc⟩ := J_eq d j
    exact ⟨c • ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, ιC E n (toL (Matrix.single i i 1)), by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum, Finset.sum_congr rfl fun i _ => uC_ιC _]
      exact hc⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG GroundTheory.Automorphic UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem tj_mem (w : Pl E) (j : ℕ) :
    Tj ℂ n (Ov E w) (exists_isUnifV w).choose j ∈ Hecke ℂ (KGL w (n := n)) := Tj_mem_hecke (exists_isUnifV w).choose_spec j

private theorem hk_apply (w : Pl E) (j : ℕ) (φ : Sm E n) :
    hk n w j φ = (qc w ^ (((j : ℂ) * ((n : ℂ) - j)) / 2))⁻¹ •
      heckeVec (rw n w) (KGL w (n := n)) (Tj ℂ n (Ov E w) (exists_isUnifV w).choose j) φ := by
  unfold hk
  rw [LinearMap.smul_apply]
  congr 1
  have hf : (Function.support fun c : GL (Fin n) (w.adicCompletion E) ⧸ KGL w (n := n) =>
      Tj ℂ n (Ov E w) (exists_isUnifV w).choose j c.out • rw n w c.out).Finite :=
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w n) (tj_mem w j).2).subset fun c hc h0 => hc (by simp [h0])
  exact (LinearMap.applyₗ (R := ℂ) φ).toAddMonoidHom.map_finsum hf

private theorem hk_comm (w : Pl E) (j : ℕ) (A : Module.End ℂ (Sm E n)) (hA : ∀ g, Commute A (rw n w g)) :
    Commute A (hk n w j) := by
  refine LinearMap.ext fun φ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, hk_apply, hk_apply, map_smul,
    map_heckeVec (Final.GLintComm E w n) (tj_mem w j) (ρ' := rw n w) A fun g y => LinearMap.congr_fun (hA g).eq y]

private theorem uC_fin (u : UC E n) (k : GL (Fin n) (Af E)) : Commute (uC E n u) (rt E n (finGL E n k)) := by
  let P := (Subalgebra.centralizer ℂ {rt E n (finGL E n k)}).comap (uC E n)
  have h1 : ∀ X, ιC E n X ∈ P := fun X => by
    rw [Subalgebra.mem_comap, uC_ιC]
    rintro _ rfl
    exact (lie_rt_fin _ _).symm
  have h : Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} ≤ P :=
    Algebra.adjoin_le (by
      rintro _ ⟨τ, i, j, rfl⟩
      rw [genC, UpperTheory.V.AlgRepEndIrreducible.eL]
      exact P.smul_mem (P.sub_mem (h1 _) (P.smul_mem (h1 _) _)) _)
  have hu : u ∈ P := h (adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top)
  exact (hu _ rfl).symm

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem kgl_eq (w : Pl E) : GLnLocal.integralGL (w.adicCompletion E) n = KGL w (n := n) := by
  have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
      GLnLocal.integralGL (w.adicCompletion E) n = GLint (Fin n) O := by
    rintro _ rfl
    rfl
  exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)

private theorem split_k (w : Pl E) (k : KA E n) : ∃ k' : GA E n, (∀ g, Commute (rt E n k') (rw n w g)) ∧
    ∃ kw ∈ KGL w (n := n), rt E n k = rt E n k' * rw n w kw := by
  set kf := GeneralLinearGroup.map (pFin E) (k : GA E n) with hkf
  set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw
  have hmem : kw ∈ KGL w (n := n) := by
    rw [← kgl_eq]
    have e : kw = Reduction.finAt w (k : GA E n) := by
      ext i j : 2
      rfl
    rw [e]
    exact k.2.2 w
  set u := kf * (locGL E n w kw)⁻¹ with hu
  have hu1 : GeneralLinearGroup.map (pLoc E w) u = 1 := by
    rw [hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]
  refine ⟨infGL E n (GeneralLinearGroup.map (pInf E) (k : GA E n)) * finGL E n u, fun g => ?_, kw, hmem, ?_⟩
  · refine Commute.map (f := rt E n) (y := finGL E n (locGL E n w g)) (Commute.mul_left (infGL_comm _ _) ?_)
    exact Commute.map (LocUniq.comm_locGL w hu1 g) (finGL E n)
  · change _ = _ * rt E n (finGL E n (locGL E n w kw))
    rw [← map_mul, mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]

private theorem rw_comm {w w' : Pl E} (e : w ≠ w') (g : GL (Fin n) (w'.adicCompletion E))
    (k : GL (Fin n) (w.adicCompletion E)) : Commute (rw n w' g) (rw n w k) :=
  Commute.map (LocUniq.comm_locGL w (pLoc_locGL_of_ne e g) k) (finRep E n)

private theorem hk_fixed (w : Pl E) (j : ℕ) {φ : Sm E n} (h : ∀ k ∈ KGL w (n := n), rw n w k φ = φ) :
    ∀ k ∈ KGL w (n := n), rw n w k (hk n w j φ) = hk n w j φ := fun k hk' => by
  rw [hk_apply, map_smul, GlobalTheory.LGrp.mem_fixed.1
    (SatCompare.heckeVec_mem_fixed (Final.GLintComm E w n) (tj_mem w j) (GlobalTheory.LGrp.mem_fixed.2 h)) k hk']

private theorem hk_zero (w : Pl E) {φ : Sm E n} (h : ∀ k ∈ KGL w (n := n), rw n w k φ = φ) : hk n w 0 φ = φ := by
  have e : Tj ℂ n (Ov E w) (exists_isUnifV w).choose 0 = dosetInd ℂ (KGL w (n := n)) 1 := by
    have d : diagJ n (exists_isUnifV w).choose 0 = 1 := by simp [diagJ]
    unfold Tj dosetInd
    congr 1
    ext g
    simp only [d, Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, mul_one, SetLike.mem_coe, ← Units.val_mul, Units.val_inj]
  rw [hk_apply, e, SatCompare.heckeVec_one (Final.GLintComm E w n) (GlobalTheory.LGrp.mem_fixed.2 h)]
  simp

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.hkOps :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.HkOps E := by
  intro E _ _ _ n w j
  refine ⟨hk_apply w j, fun u => hk_comm w j _ fun g => uC_fin u _, fun y => hk_comm w j _ fun g => ?_,
    fun S φ hw hφ => ⟨fun w' hw' k hk' => ?_, hk_zero w (hφ w hw), fun k => ⟨fun w' hw' x hx => ?_, ?_⟩, fun w' hw' j' => ?_⟩⟩
  · exact Commute.map (f := rt E n) (y := finGL E n (locGL E n w g)) (infGL_comm _ _)
  · by_cases e : w = w'
    · subst e
      exact hk_fixed w j (hφ w hw) k hk'
    · rw [← Module.End.mul_apply, (hk_comm w j _ (rw_comm e k)).eq, Module.End.mul_apply, hφ w' hw' k hk']
  · obtain ⟨k', h1, kw, h2, h3⟩ := split_k w' k
    rw [h3, Module.End.mul_apply, hφ w' hw' kw h2, ← Module.End.mul_apply, ← (h1 x).eq, Module.End.mul_apply, hφ w' hw' x hx]
  · obtain ⟨k', h1, kw, h2, h3⟩ := split_k w k
    rw [h3, Module.End.mul_apply, Module.End.mul_apply, hφ w hw kw h2, hk_fixed w j (hφ w hw) kw h2,
      ← Module.End.mul_apply, (hk_comm w j _ h1).eq, Module.End.mul_apply]
  · by_cases e : w = w'
    · subst e
      have hK := Final.GLintComm E w n
      have hf := GlobalTheory.LGrp.mem_fixed.2 (hφ w hw)
      simp only [hk_apply, SatCompare.heckeVec_smul hK (tj_mem w _)]
      rw [← SatCompare.heckeVec_conv hK (tj_mem w _) (tj_mem w _) hf, ← SatCompare.heckeVec_conv hK (tj_mem w _) (tj_mem w _) hf,
        Final.HeckeCommGL E w n ℂ _ (tj_mem w j) _ (tj_mem w j'), smul_comm]
    · exact LinearMap.congr_fun (hk_comm w' j' _ fun g => (hk_comm w j _ (rw_comm e g)).symm).eq φ
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.KilledOps
section
open NumberField

namespace UpperTheory.ConvolutionTheory.BW

private theorem finite_span_of_killed {K X : Type} {d : ℕ} (ρ : K → Matrix (Fin d) (Fin d) ℂ) (ψ : K → X → ℂ)
    (h : ∀ x : K →₀ ℂ, (x.sum fun k c => c • ρ k) = 0 → ∀ g : X, (x.sum fun k c => c * ψ k g) = 0) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ)) := by
  let A : (K →₀ ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ := Finsupp.linearCombination ℂ ρ
  let B : (K →₀ ℂ) →ₗ[ℂ] (X → ℂ) := Finsupp.linearCombination ℂ ψ
  have hAB : LinearMap.ker A ≤ LinearMap.ker B := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    funext g
    have := h x (by simpa [A, Finsupp.linearCombination_apply] using hx) g
    simpa [B, Finsupp.linearCombination_apply, Finsupp.sum_apply'] using this
  haveI : FiniteDimensional ℂ ((K →₀ ℂ) ⧸ LinearMap.ker A) :=
    Module.Finite.equiv A.quotKerEquivRange.symm
  have hr : LinearMap.range ((LinearMap.ker A).liftQ B hAB) = Submodule.span ℂ (Set.range ψ) := by
    rw [Submodule.range_liftQ]
    exact Finsupp.range_linearCombination ℂ
  rw [← hr]
  infer_instance

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW GlobalTheory.CuspRep in
theorem UpperTheory.ConvolutionTheory.BW.killedOps :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.KilledOps E := by
  intro E _ _ _ n ρ φ hφ
  refine ⟨fun k x hx g => ?_, ?_⟩
  · have h0 : ((x.mapDomain fun k' => k' * k).sum fun k' c => c • ρ.ρ k') = 0 := by
      rw [Finsupp.sum_mapDomain_index (h := fun k' c => c • ρ.ρ k') (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
      have : (x.sum fun k' c => c • ρ.ρ (k' * k)) = (x.sum fun k' c => c • ρ.ρ k') * ρ.ρ k := by
        rw [Finsupp.sum_mul]
        simp only [map_mul, smul_mul_assoc]
      rw [this, hx, zero_mul]
    have h1 := hφ _ h0 g
    rw [Finsupp.sum_mapDomain_index (h := fun (k' : KA E n) c => c * φ.1 (g * (k' : GA E n))) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)] at h1
    simp only [Subgroup.coe_mul, ← mul_assoc] at h1
    exact h1
  · unfold GroundTheory.Automorphic.AutomorphicForm.IsKFinite
    exact finite_span_of_killed ρ.ρ _ (fun x hx g => hφ x hx g)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ZSpec
section
open NumberField

theorem UpperTheory.ConvolutionTheory.BW.zSpec :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.ZSpec E := by
  intro E _ _ _ n τ
  have key : ∀ ℓ : UpperTheory.V.Cm.UC E n →ₗ[ℂ] ℂ, ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ p.coeff n = ℓ 1 ∧
      (∀ u, p.eval u = ℓ (UpperTheory.V.Cm.capC τ u)) ∧ ∀ i, ℓ (zC E n τ i) = p.coeff (n - i) := fun ℓ => by
    obtain ⟨p, h1, h2, -, h4⟩ := exists_capPoly (UpperTheory.V.Cm.genC (a := n) τ) ℓ
    refine ⟨p, h1, h2, h4, fun i => ?_⟩
    have hinj : Set.InjOn (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Finset.univ : Finset (Fin (n + 1))) :=
      fun a _ b _ h => Fin.ext (Nat.cast_injective h)
    have hd : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le h1)
    conv_rhs => rw [Lagrange.eq_interpolate hinj hd]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, zC, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul, h4, map_smul, smul_eq_mul, mul_comm]
    rfl
  refine ⟨?_, fun u => ?_⟩
  · rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    obtain ⟨p, -, h2, -, h4⟩ := key ℓ
    rw [map_sub, h4, Nat.sub_zero, h2, sub_self]
  · rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    obtain ⟨p, h1, -, h3, h4⟩ := key ℓ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, ← h3, map_sum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h1),
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, h4, smul_eq_mul, mul_comm]
    simp
end

