module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0005
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0025
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0027

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.BlockDiagonalEqLeviEmbedding
section
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.blockDiagonal_eq_leviEmbedding :
    ∀ (R : Type) [CommRing R] (r s : ℕ) (x : GL (Fin r) R) (y : GL (Fin s) R), UpperTheory.V.Af.Fin.blk x y = lev R r s (x, y) := by
  intro R _ r s x y
  have hs : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv := by
    ext (x | x) <;> simp
  have hne : ∀ (a : Fin r) (b : Fin s), Fin.castAdd s a ≠ Fin.natAdd r b := fun a b h => by
    have := congrArg Fin.val h
    have := a.isLt
    simp at *
    omega
  have h1 : (UpperTheory.V.Af.Fin.emb (UpperTheory.V.Af.Fin.e1 r s) x).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val 0 0 1) := by
    rw [UpperTheory.V.Af.Fin.coe_emb]
    ext a b
    induction a using Fin.addCases with
    | left a =>
      induction b using Fin.addCases with
      | left b =>
        have := UpperTheory.V.Af.Fin.matrixExtendByZero_apply (UpperTheory.V.Af.Fin.e1 r s) (x.val - 1) a b
        simp only [UpperTheory.V.Af.Fin.orderedCechToCatCochainsOne_apply_valueAtSubset] at this
        simp [this, Matrix.one_apply]
      | right b =>
        have := UpperTheory.V.Af.Fin.matrixExtendByZero_apply_of_outside_col (UpperTheory.V.Af.Fin.e1 r s) (x.val - 1) (Fin.castAdd s a) (j := Fin.natAdd r b) (fun k => (hne k b).symm)
        simp [this, Matrix.one_apply, hne]
    | right a =>
      have := UpperTheory.V.Af.Fin.extendByZero_apply_eq_zero_of_row_not_mem (UpperTheory.V.Af.Fin.e1 r s) (x.val - 1) (i := Fin.natAdd r a) (fun k => (hne k a).symm) b
      induction b using Fin.addCases with
      | left b => simp [this, Matrix.one_apply, (hne _ _).symm]
      | right b => simp [this, Matrix.one_apply]
  have h2 : (UpperTheory.V.Af.Fin.emb (UpperTheory.V.Af.Fin.e2 r s) y).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 y.val) := by
    rw [UpperTheory.V.Af.Fin.coe_emb]
    ext a b
    induction a using Fin.addCases with
    | right a =>
      induction b using Fin.addCases with
      | right b =>
        have := UpperTheory.V.Af.Fin.matrixExtendByZero_apply (UpperTheory.V.Af.Fin.e2 r s) (y.val - 1) a b
        simp only [UpperTheory.V.Af.Fin.alternatingToOrderedCechDegreeTwo_apply_valueAtSubset] at this
        simp [this, Matrix.one_apply]
      | left b =>
        have := UpperTheory.V.Af.Fin.matrixExtendByZero_apply_of_outside_col (UpperTheory.V.Af.Fin.e2 r s) (y.val - 1) (Fin.natAdd r a) (j := Fin.castAdd s b) (fun k => hne b k)
        simp [this, Matrix.one_apply, (hne _ _).symm]
    | left a =>
      have := UpperTheory.V.Af.Fin.extendByZero_apply_eq_zero_of_row_not_mem (UpperTheory.V.Af.Fin.e2 r s) (y.val - 1) (i := Fin.castAdd s a) (fun k => hne a k) b
      induction b using Fin.addCases with
      | left b => simp [this, Matrix.one_apply]
      | right b => simp [this, Matrix.one_apply, hne]
  refine Units.ext ?_
  rw [lev, GlobalTheory.SmGL.val_emb₂, hs, UpperTheory.V.Af.Fin.blk, Units.val_mul, h1, h2]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.DetModuleSatakeTsetEqInvPow
section
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem fst_finGL (k : GL (Fin a) (Af E)) :
    Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E a k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) k

private theorem det_finGL_any (k : GL (Fin a) (Af E)) :
    Matrix.GeneralLinearGroup.det (finGL E a k) = finId E (Matrix.GeneralLinearGroup.det k) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · have h := GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E a k)
    rw [fst_finGL] at h
    refine h.symm.trans ?_
    change _ = RingHom.fst (InfiniteAdeleRing E) (Af E) ((1 : Ad E) - sFin E 1 + sFin E _)
    have hz : ∀ x, (sFin E x).1 = 0 := fun _ => rfl
    simp only [map_one, map_sub, map_add]
    change (1 : InfiniteAdeleRing E) = 1 - (sFin E 1).1 + (sFin E (Matrix.GeneralLinearGroup.det k : Af E)).1
    simp [hz]
  · have h := GlobalTheory.CuspRep.det_map (pFin E) (finGL E a k)
    rw [pFin_finGL] at h
    refine h.symm.trans ?_
    change _ = (1 : Af E) - 1 + (Matrix.GeneralLinearGroup.det k : (Af E)ˣ)
    simp

private theorem norm_of_val_one {w : Pl E} {y : w.adicCompletion E} (h : Valued.v y = 1) : ‖y‖ = 1 := by
  rw [FinitePlace.norm_def, h, map_one, NNReal.coe_one]

private theorem norm_unif {w : Pl E} {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) : ‖ϖ‖ = (qV E w : ℝ)⁻¹ := by
  have h0 : Valued.v ϖ ≠ 0 := by
    rw [show Valued.v ϖ = _ from hu]; exact WithZero.coe_ne_zero
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  have e : Multiplicative.toAdd (WithZero.unzero h0) = -1 := by
    have : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _ :=
      (WithZero.coe_unzero h0).trans hu
    exact congrArg Multiplicative.toAdd (WithZero.coe_injective this)
  rw [WithZero.toAdd_unzero_eq_log] at e
  rw [e, zpow_neg_one]
  simp [qV]

end

theorem UpperTheory.detModule_satakeTset_eq_inv_pow :
    ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r a : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → a ≤ r → ∀ x ∈ satakeTset (n := r) w ϖ a,
      (detModule E r (finGL E r (locGL E r w x)) : ℝ) = ((qV E w : ℝ) ^ a)⁻¹ := by
  intro E _ _ w r a ϖ hu ha x hx
  obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hx
  have hm : (Matrix.GeneralLinearGroup.det x : (w.adicCompletion E)ˣ).val =
      (Matrix.GeneralLinearGroup.det k₁).val * ϖ ^ a * (Matrix.GeneralLinearGroup.det k₂).val := by
    change x.val.det = k₁.val.det * _ * k₂.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, GlobalTheory.SphGal.det_diagJ ϖ ha]
  have hid : Matrix.GeneralLinearGroup.det (finGL E r (locGL E r w x)) =
      GroundTheory.Global.IdeleGroup.finiteEmbedding w (Matrix.GeneralLinearGroup.det x) :=
    (det_finGL_any _).trans (finId_det_locGL w x)
  have hmod : (detModule E r (finGL E r (locGL E r w x)) : ℝ) =
      ‖((Matrix.GeneralLinearGroup.det x : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ := by
    change ((GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det (finGL E r (locGL E r w x))) : {r : ℝ // 0 < r}) : ℝ) = _
    rw [hid, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding]
  have n₁ : ‖(Matrix.GeneralLinearGroup.det k₁).val‖ = 1 :=
    norm_of_val_one (GlobalTheory.SphGal.isUnitAt_det_of_mem (k := k₁) h₁)
  have n₂ : ‖(Matrix.GeneralLinearGroup.det k₂).val‖ = 1 :=
    norm_of_val_one (GlobalTheory.SphGal.isUnitAt_det_of_mem (k := k₂) h₂)
  rw [hmod, hm, norm_mul, norm_mul, n₁, n₂, norm_pow, norm_unif hu, one_mul, mul_one, inv_pow]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsSatakeTsetSumEigenvector
section
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private def zGL {L : Type} [Field L] (r : ℕ) {π : L} (hπ : π ≠ 0) : GL (Fin r) L :=
  Units.map ((Matrix.scalar (Fin r) : L →+* Matrix (Fin r) (Fin r) L) : L →* Matrix (Fin r) (Fin r) L) (Units.mk0 π hπ)

private theorem zGL_val {L : Type} [Field L] (r : ℕ) {π : L} (hπ : π ≠ 0) :
    ((zGL r hπ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) = Matrix.diagonal fun _ => π := rfl

private theorem zGL_comm {L : Type} [Field L] (r : ℕ) {π : L} (hπ : π ≠ 0) (g : GL (Fin r) L) :
    zGL r hπ * g = g * zGL r hπ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, zGL_val]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

private theorem card_top {r a : ℕ} (h : a ≤ r) :
    ((Finset.univ.filter fun i : Fin r => (i : ℕ) < r - a)ᶜ).card = a := by
  rw [Finset.card_compl, Fintype.card_fin, Fin.card_filter_val_lt]
  omega

private theorem inv_mem {E : Type} [Field E] [NumberField E] (w : Pl E) {r a : ℕ} (har : a ≤ r)
    {ϖ : w.adicCompletion E} (hπ : ϖ ≠ 0) {b : GL (Fin r) (w.adicCompletion E)}
    (hb : b ∈ satakeTset w ϖ (r - a)) : b⁻¹ * zGL r hπ ∈ satakeTset w ϖ a := by
  classical
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hb
  set S : Finset (Fin r) := (Finset.univ.filter fun i : Fin r => (i : ℕ) < r - a)ᶜ with hSdef
  have hS : S.card = a := card_top har
  set G := satakeGL (Ov E w) hπ S (fun _ => 0) with hGdef
  have hG : G ∈ satakeTset w ϖ a := by
    obtain ⟨x, hx, y, hy, e'⟩ := satakeGL_mem_doset (Ov E w) hπ S (fun _ => 0)
    rw [hS] at e'
    exact ⟨x, hx, y, hy, e'⟩
  have hGv : (G : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = satakeD ϖ S := by
    have h0 : satakeN (Ov E w) S (fun _ => 0) = 0 := by
      ext i j
      simp [satakeN]
    show (1 + satakeN (Ov E w) S (fun _ => 0)) * satakeD ϖ S = _
    rw [h0, add_zero, Matrix.one_mul]
  set d : GL (Fin r) (w.adicCompletion E) := k₁⁻¹ * b * k₂⁻¹ with hddef
  have hd : (d : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = diagJ r ϖ (r - a) := by
    rw [hddef, Units.val_mul, Units.val_mul, e]
    have h1 : ((k₁⁻¹ : GL (Fin r) (w.adicCompletion E)) : Matrix (Fin r) (Fin r) (w.adicCompletion E)) *
        (k₁ : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (k₂ : Matrix (Fin r) (Fin r) (w.adicCompletion E)) *
        ((k₂⁻¹ : GL (Fin r) (w.adicCompletion E)) : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hGd : G * d = zGL r hπ := by
    apply Units.ext
    rw [Units.val_mul, hGv, hd, zGL_val]
    unfold satakeD diagJ
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : (i : ℕ) < r - a
    · simp [hSdef, h]
      intro h'
      omega
    · simp [hSdef, h]
      intro h'
      omega
  have hb' : b = k₁ * d * k₂ := by
    rw [hddef]; group
  have hz : d⁻¹ * zGL r hπ = G := by
    rw [← zGL_comm, ← hGd]; group
  have hfin : b⁻¹ * zGL r hπ = k₂⁻¹ * G * k₁⁻¹ := by
    rw [← hz, hb', mul_inv_rev, mul_inv_rev]
    have := zGL_comm r hπ k₁⁻¹
    simp only [mul_assoc]
    rw [← this]
  rw [hfin]
  exact satake_Tset_right w (satake_Tset_left w hG ((GLint _ _).inv_mem hk₂)) ((GLint _ _).inv_mem hk₁)

theorem UpperTheory.exists_satakeTset_sum_eigenvector :
    ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r a : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → a ≤ r →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (f : V) (B : Multiset ℂˣ), IsSatVecGL w ρ f B →
      ∃ (n : ℕ) (c : Fin n → GL (Fin r) (w.adicCompletion E)) (μ : ℂ), 0 < n ∧ (∀ i, (c i)⁻¹ ∈ satakeTset w ϖ a) ∧ ∑ i, ρ (c i) f = μ • f := by
  intro E _ _ w r a ϖ hu har V _ _ ρ f B hf
  classical
  obtain ⟨hf0, hfix, -, hT⟩ := hf
  have hϖ := mem_Ov_of_isUnifV hu
  have hπ : ϖ ≠ 0 := satake_unif_ne_zero w hu
  letI : Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) := @Fintype.ofFinite _ (satake_res_finite w hϖ hu)
  have hne : ∀ j, j ≤ r → Nonempty (SatakeIdx w hϖ (n := r) j) := by
    intro j hj
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin r))) (n := j)
      (by simpa using hj)
    exact ⟨⟨⟨S, hS⟩, fun _ => 0⟩⟩
  have hsum : ∀ j, j ≤ r → ∑ i : SatakeIdx w hϖ (n := r) j, ρ (satakeB w hϖ hu i) f =
      satEig (qV E w) r B j • f := fun j hj => by
    rw [← UpperTheory.V.Cj.S.hkSum E w r V ρ ϖ hϖ hu j hj f hfix, hT ϖ hu j hj]
  set z := zGL r hπ with hzdef
  have hfx : ∀ k ∈ KGL w (n := r), ρ k f = f := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hfix _ hk
  have hB : ∀ i : SatakeIdx w hϖ (n := r) r, ρ (satakeB w hϖ hu i) f = ρ z f := by
    intro i
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := satakeB_mem w hϖ hu i
    have hdz : diagJ r ϖ r = (z : Matrix (Fin r) (Fin r) (w.adicCompletion E)) := by
      rw [hzdef, zGL_val]
      unfold diagJ
      congr 1
      funext i
      simp [i.isLt]
    have : satakeB w hϖ hu i = z * (k₁ * k₂) := by
      apply Units.ext
      rw [e, hdz, ← Units.val_mul, ← Units.val_mul, hzdef, ← zGL_comm, mul_assoc]
    rw [this, map_mul, Module.End.mul_apply, hfx _ ((KGL w (n := r)).mul_mem hk₁ hk₂)]
  obtain ⟨i₀⟩ := hne r le_rfl
  have hcard : (Fintype.card (SatakeIdx w hϖ (n := r) r) : ℂ) ≠ 0 := by
    have : Fintype.card (SatakeIdx w hϖ (n := r) r) ≠ 0 := by
      haveI : Nonempty (SatakeIdx w hϖ (n := r) r) := ⟨i₀⟩
      exact Fintype.card_ne_zero
    exact_mod_cast this
  set c : ℂ := (Fintype.card (SatakeIdx w hϖ (n := r) r) : ℂ)⁻¹ * satEig (qV E w) r B r with hcdef
  have hzf : ρ z f = c • f := by
    have h := hsum r le_rfl
    simp only [hB, Finset.sum_const, Finset.card_univ] at h
    rw [hcdef, mul_smul, ← h, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hzf
    apply hf0
    have : ρ z⁻¹ (ρ z f) = f := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this, hzf, map_zero]
  have hzi : ρ z⁻¹ f = c⁻¹ • f := by
    have : ρ z⁻¹ (ρ z f) = f := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hzf, map_smul] at this
    rw [eq_inv_smul_iff₀ hc]
    exact this
  obtain ⟨i₁⟩ := hne (r - a) (Nat.sub_le _ _)
  let e := Fintype.equivFin (SatakeIdx w hϖ (n := r) (r - a))
  refine ⟨Fintype.card (SatakeIdx w hϖ (n := r) (r - a)), fun i => z⁻¹ * satakeB w hϖ hu (e.symm i),
    satEig (qV E w) r B (r - a) * c⁻¹, Fintype.card_pos_iff.2 ⟨i₁⟩, fun i => ?_, ?_⟩
  · rw [mul_inv_rev, inv_inv]
    exact inv_mem w har hπ (satakeB_mem w hϖ hu _)
  · rw [Equiv.sum_comp e.symm (fun i => ρ (z⁻¹ * satakeB w hϖ hu i) f)]
    simp only [map_mul, Module.End.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hsum _ (Nat.sub_le _ _), map_smul, hzi, smul_smul]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegrableTranslateMulConjAndInnerSelfNeZero
section
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private theorem out_eq_cuspQuot {E : Type} [Field E] [NumberField E] {r : ℕ}
    (F : AdelicGLn.AdelicGL E r → ℂ) (h : AutomorphicForm.IsLeftInvariant F)
    (y : RightCosetSpace (rationalGLOne (K := E) (n := r))) :
    F ((Quotient.out y : normOneGL (K := E) (n := r)) : AdelicGLn.AdelicGL E r) = CuspidalSpectrum.cuspQuot h y := by
  have e : RightCosetSpace.mk (rationalGLOne (K := E) (n := r)) (Quotient.out y) = y := Quotient.out_eq y
  calc F ((Quotient.out y : normOneGL (K := E) (n := r)) : AdelicGLn.AdelicGL E r)
      = CuspidalSpectrum.cuspQuot h (RightCosetSpace.mk (rationalGLOne (K := E) (n := r)) (Quotient.out y)) := rfl
    _ = CuspidalSpectrum.cuspQuot h y := by rw [e]

theorem UpperTheory.integrable_translate_mul_conj_and_inner_self_ne_zero :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Set (Pl E)) (r : ℕ) (b : Blo S r),
      (∀ g : GA E r, Integrable (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => b.f.1 (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r))) (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r))) ∧
      ∫ y : RightCosetSpace (rationalGLOne (K := E) (n := r)), b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r)) ∂(quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) ≠ 0 := by
  intro E _ _ _ S r b
  have : OpensMeasurableSpace (RightCosetSpace (rationalGLOne (K := E) (n := r))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  have hfin := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
  have hcont : Continuous b.f.1 := b.cusp.1.continuous
  have hL : AutomorphicForm.IsLeftInvariant b.f.1 := b.cusp.1.isLeftInvariant
  obtain ⟨C, hC⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms b.cusp
  have hsec : ∀ s : {x : ℝ // 0 < x}, centralSection E r s = zt E r (Real.log s.1) := fun s => by
    unfold zt
    exact congrArg _ (Subtype.ext (Real.exp_log s.2).symm)
  have hb : ∀ g, ‖b.f.1 g‖ ≤ C := fun g => by
    obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL g
    rw [hsec s, b.cen]
    exact hC y hy
  have hbq : ∀ (F : AdelicGLn.AdelicGL E r → ℂ) (h : AutomorphicForm.IsLeftInvariant F), (∀ g, ‖F g‖ ≤ C) →
      ∀ q, ‖CuspidalSpectrum.cuspQuot h q‖ ≤ C := fun F h hF q => by
    rw [← out_eq_cuspQuot F h q]
    exact hF _
  have hq := CuspidalSpectrum.continuous_cuspQuot hL hcont
  refine ⟨fun g => ?_, fun h0 => ?_⟩
  · have hLg : AutomorphicForm.IsLeftInvariant (fun x => b.f.1 (x * g)) := fun γ x => by
      show b.f.1 (_ * x * g) = b.f.1 (x * g)
      rw [mul_assoc]
      exact hL γ _
    have hcg : Continuous (fun x : AdelicGLn.AdelicGL E r => b.f.1 (x * g)) :=
      hcont.comp (continuous_id.mul continuous_const)
    have hqg := CuspidalSpectrum.continuous_cuspQuot hLg hcg
    have e : (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => b.f.1 (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r))) =
        fun y => CuspidalSpectrum.cuspQuot hLg y * starRingEnd ℂ (CuspidalSpectrum.cuspQuot hL y) := by
      funext y
      rw [← out_eq_cuspQuot _ hLg y, ← out_eq_cuspQuot _ hL y]
    rw [e]
    refine Integrable.of_bound (hqg.mul (Complex.continuous_conj.comp hq)).aestronglyMeasurable (C * C)
      (Filter.Eventually.of_forall fun q => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hbq _ hLg (fun x => hb _) q) (hbq _ hL hb q) (norm_nonneg _)
      ((norm_nonneg _).trans (hbq _ hL hb q))
  · have e : ∀ y : RightCosetSpace (rationalGLOne (K := E) (n := r)),
        b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r)) =
        ((‖CuspidalSpectrum.cuspQuot hL y‖ ^ 2 : ℝ) : ℂ) := fun y => by
      rw [out_eq_cuspQuot _ hL y, Complex.mul_conj', Complex.ofReal_pow]
    have h1 : ∫ q, ‖CuspidalSpectrum.cuspQuot hL q‖ ^ 2 ∂(quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) = 0 := by
      rw [← Complex.ofReal_eq_zero, ← integral_complex_ofReal, ← h0]
      exact integral_congr_ae (Filter.Eventually.of_forall fun q => (e q).symm)
    have hi : Integrable (fun q => ‖CuspidalSpectrum.cuspQuot hL q‖ ^ 2) (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) :=
      Integrable.of_bound (hq.norm.pow 2).aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun q => by
        rw [norm_pow, norm_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbq _ hL hb q) 2)
    have h2 := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg _) hi).1 h1
    have h3 := MeasureTheory.QuasiMeasurePreserving.ae_eq_comp
      (RightCosetSpace.quasiMeasurePreserving_mk (rationalGLOne (K := E) (n := r)) (mu1 E r)) h2
    have h4 := (Continuous.ae_eq_iff_eq (mu1 E r) (f := fun y : normOneGL (K := E) (n := r) => ‖b.f.1 (y : AdelicGLn.AdelicGL E r)‖ ^ 2)
      ((hcont.comp continuous_subtype_val).norm.pow 2) continuous_const).1 h3
    apply b.ne
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL g
    rw [hsec s, b.cen]
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (congrFun h4 ⟨y, hy⟩))
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegralQuotientRightTranslateEqAndIntegrableIff
section
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.integral_quotient_rightTranslate_eq_and_integrable_iff :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (h : GA E r → ℂ), AutomorphicForm.IsLeftInvariant h → ∀ g ∈ normOneGL (K := E) (n := r),
      (∫ y : RightCosetSpace (rationalGLOne (K := E) (n := r)), h (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g) ∂(quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) = ∫ y : RightCosetSpace (rationalGLOne (K := E) (n := r)), h ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) ∂(quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r))) ∧
      (Integrable (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => h (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g)) (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) ↔ Integrable (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => h ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r)) (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r))) := by
  intro E _ _ r h hh g hg
  have e1 : (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => h ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r)) =
      CuspidalSpectrum.cuspQuot hh := by
    funext y
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  have e2 : (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => h (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g)) =
      CuspidalSpectrum.cuspQuot hh ∘ rightMul (rationalGLOne (K := E) (n := r)) ⟨g, hg⟩ := by
    funext y
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  have hm := measurePreserving_rightMul (Γ := rationalGLOne (K := E) (n := r)) (mu1 E r) ⟨g, hg⟩
  have he : MeasurableEmbedding (rightMul (rationalGLOne (K := E) (n := r)) ⟨g, hg⟩) :=
    by
      set_option synthInstance.maxHeartbeats 200000 in
        exact (rightMulHomeomorph (rationalGLOne (K := E) (n := r)) ⟨g, hg⟩).measurableEmbedding
  rw [e1, e2]
  exact ⟨hm.integral_comp he _, hm.integrable_comp_emb he⟩
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.SetIntegralRestrictMulThetaKernelEqUnfolded
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem cont_em {E : Type} [Field E] [NumberField E] : Continuous (em E) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id AdeleBaseChange.continuous_adeleMap)

private theorem ex_rat {E : Type} [Field E] [NumberField E] (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) :
    ∃ γ', em E (gl (ratS ℚ γ)) = ratGL E 2 γ' := by
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap ℚ E) (Matrix.SpecialLinearGroup.toGL γ), ?_⟩
  apply Units.ext
  ext i j
  rw [ratGL_apply]
  exact AdeleBaseChange.adeleMap_algebraMap _

private theorem glm (g h : G1 ℚ) : gl (g * h) = gl g * gl h := map_mul _ _ _

private theorem row_nU (b : A ℚ) (h : GL (Fin 2) (A ℚ)) (j : Fin 2) : (gl (nU b) * h).val 1 j = h.val 1 j := by
  rw [Units.val_mul, M.val_gl]
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two]

private theorem row_rat (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (h : GL (Fin 2) (A ℚ)) (j : Fin 2) :
    (gl (ratS ℚ γ) * h).val 1 j = ((fun i => rt (γ.1 1 i)) ᵥ* h.val) j := by
  rw [Units.val_mul, M.val_gl, M.val_ratS]
  rfl

theorem UpperTheory.setIntegral_restrict_mul_thetaKernel_eq_unfolded :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        ∫ g in M₀.D, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) ∂M₀.μ = ∫ p, Un.Tt φ Φ t u p ∂M₀.ν := by
  intro E _ _ D ω φ hA M₀ Φ hΦ t u hu
  obtain ⟨σ, hσ⟩ := G.exists_rowSec (F := ℚ)
  obtain ⟨hmp, hme⟩ := UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact M₀ t u hu
  have hleft : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (h : GL (Fin 2) (A ℚ)), φ (em E (gl (ratS ℚ γ) * h)) = φ (em E h) := by
    intro γ h
    obtain ⟨γ', e⟩ := ex_rat (E := E) γ
    rw [map_mul, e, hA.left]
  have hg : Continuous fun g : G1 ℚ => gl g * dM u := M.continuous_gl.mul continuous_const
  have hm : Measurable (Un.Uu φ Φ t u) := by
    refine Continuous.measurable ?_
    refine (hA.cont.comp (cont_em.comp hg)).mul ((continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j => ?_))
    exact continuous_const.mul ((Units.continuous_val.comp hg).matrix_elem 1 j)
  have hinv : ∀ (ξ : ℚ) g, Un.Uu φ Φ t u (nU (rt ξ) * g) = Un.Uu φ Φ t u g := by
    intro ξ g
    have e : gl (nU (rt ξ) * g) * dM u = gl (nU (rt ξ)) * (gl g * dM u) := by rw [glm, mul_assoc]
    have e' : φ (em E (gl (nU (rt ξ)) * (gl g * dM u))) = φ (em E (gl g * dM u)) := by
      rw [← M.ratS_up]
      exact hleft _ _
    unfold Un.Uu
    rw [e, e']
    simp only [row_nU]
  have key := (M.unfC ℚ M₀ σ (Un.Uu φ Φ t u) hσ hm hinv (UpperTheory.maximalCompact_integral_unipotent_norm_finite E D ω φ hA M₀ Φ hΦ t u hu)).2.2.2
  have e1 : ∀ g, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) = ∑' r, Un.Uu φ Φ t u (ratS ℚ (σ r) * g) := by
    intro g
    unfold ThR
    rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    have e : gl (ratS ℚ (σ r) * g) * dM u = gl (ratS ℚ (σ r)) * (gl g * dM u) := by rw [glm, mul_assoc]
    unfold Un.Uu
    rw [e, hleft]
    simp only [row_rat]
    rw [hσ r]
  simp only [e1]
  rw [key, Meas.I0, ← hmp.integral_comp hme]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have e2 : ∀ b, gl (nU b * (mD (Un.aa t u p.1) * cD u p.2)) * dM u =
      gl (nU b) * (gl (mD (Un.aa t u p.1)) * dM u * gl p.2) := by
    intro b
    rw [glm, glm, mul_assoc, mul_assoc, M.gl_cD, mul_assoc]
  simp only [iw, Un.Tt, Un.Uu, Un.Fb, e2, row_nU]
  rw [integral_mul_const, ← mul_assoc]
  simp only [map_mul (em E) (gl (nU _))]
end

