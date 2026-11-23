module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LevelSplit
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.levelSplit :
    UpperTheory.V.Cj.S.LevelSplit := by
  intro E _ _ a L hL
  have ho : IsOpen ((L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a : Subgroup (GL (Fin a) (Af E))) :
      Set (GL (Fin a) (Af E))) := hL.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a)
  have hev := LocSph.eventually_mem (ho.mem_nhds (one_mem _))
  refine ⟨_, ho, inf_le_left, _, Filter.eventually_cofinite.1 hev, fun w hw => ?_⟩
  have hw' := not_not.1 hw
  have h1 : ∀ k ∈ KGL w (n := a), locGL E a w k ∈ L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a := by
    rintro _ ⟨g, rfl⟩
    exact hw' g
  refine ⟨h1, fun u hu => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc E w) u ∈ KGL w (n := a) := by
    obtain ⟨h2, h3⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E a).1 hu.2
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · exact h2 i j w
    · rw [← map_inv]
      exact h3 i j w
  exact ⟨_, hk, _, mul_mem (inv_mem (h1 _ hk)) hu, LocEx.map_pLoc_inv_mul w u, (mul_inv_cancel_left _ _).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LieEqLam
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

open UpperTheory.V UpperTheory.V.Af.Fin in
private theorem lie_eq_lam {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (i j : Fin a) (x : Cinf E)
    (φ : Sm E a) :
    Cm.smEq E a (lie E a (toL (Matrix.single i j x)) φ) =
      lam E a (Matrix.single i j (Cm.mixEq E x)) (Cm.smEq E a φ) := by
  rw [← Cm.uAction_ι_smEq, lam_apply]
  congr 3
  refine Subtype.ext (Matrix.ext fun k l => ?_)
  change Cm.mixEq E (Matrix.single i j x k l) = Matrix.single i j (Cm.mixEq E x) k l
  simp only [Matrix.single_apply, apply_ite (Cm.mixEq E), map_zero]

open UpperTheory.V UpperTheory.V.Af.Fin in
theorem UpperTheory.V.Cj.S.slice :
    UpperTheory.V.Cj.S.Slice := by
  intro E _ _ _ a n e g
  obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie E a n e g
  have key : ∀ i j x ψ, (Cm.smEq E a).symm (f (Cm.smEq E n (lie E n (toL (Matrix.single (e i) (e j) x)) ψ))) =
      lie E a (toL (Matrix.single i j x)) ((Cm.smEq E a).symm (f (Cm.smEq E n ψ))) := fun i j x ψ => by
    rw [LinearEquiv.symm_apply_eq, lie_eq_lam, lie_eq_lam, LinearEquiv.apply_symm_apply, ← matrixExtendByZero_single, hl]
  refine ⟨(Cm.smEq E a).symm.toLinearMap ∘ₗ f ∘ₗ (Cm.smEq E n).toLinearMap, fun ψ x => hf _ x, fun t i j ψ => ?_⟩
  rw [← Cm.uC_genC, ← Cm.uC_genC]
  simp only [Cm.genC, AlgRepEndIrreducible.eL, map_smul, map_sub, Cm.uC_ιC, LinearMap.smul_apply, LinearMap.sub_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LocComm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem kgl_eq (w : Pl E) :
    GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a = KGL w (n := a) := by
  have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
      GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a = GLint (Fin a) O := by
    rintro _ rfl
    rfl
  exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)

private theorem loc_comm (w : Pl E) (g : GL (Fin a) (w.adicCompletion E)) {u : GL (Fin a) (Af E)}
    (hu : GeneralLinearGroup.map (pLoc E w) u = 1) : u * locGL E a w g = locGL E a w g * u := by
  have H : ∀ v, GeneralLinearGroup.map (pLoc E v) (u * locGL E a w g) =
      GeneralLinearGroup.map (pLoc E v) (locGL E a w g * u) := fun v => by
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [hu, mul_one, one_mul]
    · rw [pLoc_locGL_of_ne hv, mul_one, one_mul]
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun v => congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) (H v)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.rtK :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.RtK := by
  intro hc E _ _ _ a φ m B h k hk
  have hne : rt E a k φ ≠ 0 := fun e => h.ne (by
    have := congrArg (rt E a k⁻¹) e
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this)
  refine ⟨hne, (Cm.isAutForm_iff _).2 (((Cm.isAutForm_iff _).1 h.aut).rightTranslate_of_mem_maxCompact hk),
    fun t => ⟨(h.cap t).1, fun u => ?_⟩, h.sat.mono fun w hw => ?_⟩
  · have e := LinearMap.congr_fun ((hc E a t u).1 k).eq φ
    simp only [Module.End.mul_apply] at e
    rw [e, (h.cap t).2 u, map_smul]
  · set kf := GeneralLinearGroup.map (pFin E) k with hkf
    set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw
    have hmem : kw ∈ KGL w (n := a) := by
      rw [← kgl_eq]
      have e : kw = GroundTheory.Automorphic.Reduction.finAt w k := by
        ext i j : 2
        rfl
      rw [e]
      exact hk.2 w
    set u := kf * (locGL E a w kw)⁻¹ with hu
    have hu1 : GeneralLinearGroup.map (pLoc E w) u = 1 := by
      rw [hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]
    set k' := infGL E a (GeneralLinearGroup.map (pInf E) k) * finGL E a u with hk'
    have hdec : k' * finGL E a (locGL E a w kw) = k := by
      rw [hk', mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]
    have hfix : rt E a (finGL E a (locGL E a w kw)) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hw.2.1 kw hmem
    have e : rt E a k' φ = rt E a k φ := by
      conv_rhs => rw [← hdec, map_mul (rt E a), Module.End.mul_apply, hfix]
    rw [← e] at hne ⊢
    refine hw.map (rt E a k') (fun g y => ?_) hne
    change rt E a k' (rt E a (finGL E a (locGL E a w g)) y) = rt E a (finGL E a (locGL E a w g)) (rt E a k' y)
    have hcm : k' * finGL E a (locGL E a w g) = finGL E a (locGL E a w g) * k' := by
      rw [hk', mul_assoc, ← map_mul (finGL E a), loc_comm w g hu1, map_mul (finGL E a), ← mul_assoc, ← mul_assoc,
        infGL_comm _ (locGL E a w g)]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul (rt E a), ← map_mul (rt E a), hcm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.MatBlock
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

private theorem cn_ne {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp at this
  omega

private theorem block_embedding_first_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin r) R) :
    (emb (e1 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m.val 0 0 1) := by
  ext i j
  rw [coe_emb, Matrix.add_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have := matrixExtendByZero_apply (e1 r s) (m.val - 1) i j
    simp only [orderedCechToCatCochainsOne_apply_valueAtSubset] at this
    rw [this]
    simp [Matrix.one_apply]
  · rw [matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cn_ne k j).symm]
    simp [Matrix.one_apply_ne (cn_ne i j)]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne k i).symm]
    simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne k i).symm]
    simp [Matrix.one_apply]

private theorem block_embedding_second_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin s) R) :
    (emb (e2 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 m.val) := by
  ext i j
  rw [coe_emb, Matrix.add_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne i k)]
    simp [Matrix.one_apply]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne i k)]
    simp [Matrix.one_apply_ne (cn_ne i j)]
  · rw [matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cn_ne j k)]
    simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · have := matrixExtendByZero_apply (e2 r s) (m.val - 1) i j
    simp only [alternatingToOrderedCechDegreeTwo_apply_valueAtSubset] at this
    rw [this]
    simp [Matrix.one_apply]

private theorem unip_val {R : Type} [CommRing R] {r s : ℕ} (Y : Matrix (Fin r) (Fin s) R) :
    ∃ X : UPos (r + s) r → R,
      unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 Y 0 1) := by
  refine ⟨fun p => Y ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.2.2; have := p.1.2.2; omega⟩, ?_⟩
  ext i j
  rw [unipMatrix, Matrix.add_apply, blockEntry_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply_ne (cn_ne i j)]
  · simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · simp [Matrix.one_apply]

private theorem block_form {R : Type} [CommRing R] {r s : ℕ} (b : GL (Fin (r + s)) R) (m₁ : GL (Fin r) R)
    (m₂ : GL (Fin s) R) (h₁ : ∀ i j, b.val (Fin.castAdd s i) (Fin.castAdd s j) = m₁.val i j)
    (h₂ : ∀ i j, b.val (Fin.natAdd r i) (Fin.natAdd r j) = m₂.val i j)
    (h₀ : ∀ i j, b.val (Fin.natAdd r i) (Fin.castAdd s j) = 0) :
    ∃ X : UPos (r + s) r → R, b = unipGL X * blk m₁ m₂ := by
  let B : Matrix (Fin r) (Fin s) R := b.val.submatrix (Fin.castAdd s) (Fin.natAdd r)
  have hb' : b.val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m₁.val B 0 m₂.val) := by
    ext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [h₁]
    · simp [B]
    · simp [h₀]
    · simp [h₂]
  obtain ⟨X, hX⟩ := unip_val (B * (m₂⁻¹).val)
  refine ⟨X, Units.ext ?_⟩
  rw [blk, Units.val_mul, Units.val_mul, coe_unipGL, hX, block_embedding_first_val, block_embedding_second_val, hb']
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.matBlock :
    UpperTheory.V.Cj.S.MatBlock := by
  intro L _ O r s π hπ S c
  refine block_form _ _ _ (fun i j => ?_) (fun i j => ?_) fun i j => ?_
  · have hm : ∀ k, k ∈ sub1 S ↔ Fin.castAdd s k ∈ S := fun k => by simp [sub1]
    have hN : satakeN O S c (Fin.castAdd s i) (Fin.castAdd s j) = satakeN O (sub1 S) (c ∘ pair1 S) i j := by
      unfold satakeN
      by_cases h : i ∈ sub1 S ∧ j ∉ sub1 S ∧ i < j
      · rw [dite_eq_left h, dite_eq_left ⟨(hm i).1 h.1, fun h' => h.2.1 ((hm j).2 h'), h.2.2⟩]
        rfl
      · rw [dite_eq_right h, dite_eq_right fun h' => h ⟨(hm i).2 h'.1, fun h'' => h'.2.1 ((hm j).1 h''), h'.2.2⟩]
    rw [satakeGL_apply, satakeGL_apply, hN]
    simp [Matrix.one_apply, hm]
  · have hm : ∀ k, k ∈ sub2 S ↔ Fin.natAdd r k ∈ S := fun k => by simp [sub2]
    have hN : satakeN O S c (Fin.natAdd r i) (Fin.natAdd r j) = satakeN O (sub2 S) (c ∘ pair2 S) i j := by
      unfold satakeN
      by_cases h : i ∈ sub2 S ∧ j ∉ sub2 S ∧ i < j
      · rw [dite_eq_left h, dite_eq_left ⟨(hm i).1 h.1, fun h' => h.2.1 ((hm j).2 h'), Nat.add_lt_add_left h.2.2 r⟩]
        rfl
      · rw [dite_eq_right h, dite_eq_right fun h' => h ⟨(hm i).2 h'.1, fun h'' => h'.2.1 ((hm j).1 h''),
          Nat.lt_of_add_lt_add_left h'.2.2⟩]
    rw [satakeGL_apply, satakeGL_apply, hN]
    simp [Matrix.one_apply, hm]
  · apply satakeGL_lower
    change (Fin.castAdd s j).val < (Fin.natAdd r i).val
    simp
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.MemFixed
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem mem_fixed' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H : Subgroup G} {v : V} : v ∈ fixed ρ H ↔ ∀ k ∈ H, ρ k v = v := by
  change (∀ h : H, ρ (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp

private theorem blk_mul {r s : ℕ} {R : Type} [CommRing R] (a a' : GL (Fin r) R) (b b' : GL (Fin s) R) :
    blk (a * a') (b * b') = blk a b * blk a' b' := by
  simp only [blk, map_mul, mul_assoc]
  rw [← mul_assoc (emb (e2 r s) b), ← UpperTheory.V.Af.Fin.emb_comm, mul_assoc]

private theorem fL_apply {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (w : Pl E)
    (b : GL (Fin n) (w.adicCompletion E)) (φ : Sm E n) (x : GA E n) :
    (fL n w b φ).1 x = φ.1 (x * finGL E n (locGL E n w b)) := rfl

private theorem tOp_apply (hS : HkSum) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (w : Pl E)
    {ϖ : w.adicCompletion E} (hϖ : ϖ ∈ Ov E w) (hu : IsUnifV E w ϖ) [Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩)] (j : ℕ)
    (hj : j ≤ n) (φ : Sm E n) (hφ : φ ∈ fixed (fL n w) (KGL w (n := n))) (x : GA E n) :
    (tOp n w hu j φ).1 x =
      ∑ i : SatakeIdx w hϖ (n := n) j, φ.1 (x * finGL E n (locGL E n w (satakeB w hϖ hu i))) := by
  have h := hS E w n (Sm E n) (fL n w) ϖ hϖ hu j hj φ hφ
  have h' : tOp n w hu j φ = ∑ i : SatakeIdx w hϖ (n := n) j, fL n w (satakeB w hϖ hu i) φ := h
  rw [h', Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem UpperTheory.V.Cj.S.hkRel :
    UpperTheory.V.Cj.S.Slice → UpperTheory.V.Cj.S.HkSum → UpperTheory.V.Cj.S.HkLocal → UpperTheory.V.Cj.S.HeckeLocalBlock → UpperTheory.V.Cj.S.HkRel := by
  intro hSl hS hL hB E _ _ _ r s ψ hN w hψ ϖ hu j hj
  have hϖ : ϖ ∈ Ov E w := mem_Ov_of_isUnifV hu
  have := satake_res_finite w hϖ hu
  letI : Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) := Fintype.ofFinite _
  obtain ⟨b1, b2, b3, b4⟩ := hB E w r s
  have hfix : ∀ k ∈ KGL w (n := (r + s)), ∀ g, ψ.1 (g * finGL E _ (locGL E _ w k)) = ψ.1 g := fun k hk g =>
    congrFun (congrArg Subtype.val (mem_fixed'.1 hψ k hk)) g
  have hs1 : ∀ y : GA E s, ∃ f : Sm E r, (∀ x, f.1 x = ψ.1 (blk x y)) ∧ f ∈ fixed (fL r w) (KGL w (n := r)) := fun y => by
    obtain ⟨f, hf, -⟩ := hSl E r (r + s) (e1 r s) (emb (e2 r s) y)
    have hf' : ∀ x, (f ψ).1 x = ψ.1 (blk x y) := fun x => by rw [hf, blk, UpperTheory.V.Af.Fin.emb_comm]
    refine ⟨f ψ, hf', mem_fixed'.2 fun k hk => Subtype.ext (funext fun x => ?_)⟩
    rw [fL_apply, hf', hf', ← hfix _ (b4 k hk 1 (one_mem _)) (blk x y), b1, ← blk_mul, map_one, map_one, mul_one]
  have hs2 : ∀ x : GA E r, ∃ f : Sm E s, (∀ y, f.1 y = ψ.1 (blk x y)) ∧ f ∈ fixed (fL s w) (KGL w (n := s)) := fun x => by
    obtain ⟨f, hf, -⟩ := hSl E s (r + s) (e2 r s) (emb (e1 r s) x)
    have hf' : ∀ y, (f ψ).1 y = ψ.1 (blk x y) := fun y => by rw [hf, blk]
    refine ⟨f ψ, hf', mem_fixed'.2 fun k hk => Subtype.ext (funext fun y => ?_)⟩
    rw [fL_apply, hf', hf', ← hfix _ (b4 1 (one_mem _) k hk) (blk x y), b1, ← blk_mul, map_one, map_one, mul_one]
  choose f2 hf2 hf2' using hs2
  refine ⟨fun p x y => ∑ i₁ : SatakeIdx w hϖ (n := r) p.1, ∑ i₂ : SatakeIdx w hϖ (n := s) p.2,
    ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) (y * finGL E s (locGL E s w (satakeB w hϖ hu i₂)))),
    fun p => ⟨fun x y => ∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
      ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) y), fun y => ?_, fun x => ?_⟩, fun x y => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := hs1 y
    refine ⟨f, funext hf, funext fun x => ?_⟩
    rw [tOp_apply hS w hϖ hu _ (Nat.lt_succ_iff.mp p.1.2) f hf']
    simp only [hf]
  · have hv : ∀ y, (∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
        f2 (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁)))).1 y = ∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
        ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) y) := fun y => by
      rw [Submodule.coe_sum, Finset.sum_apply]
      simp only [hf2]
    refine ⟨_, funext hv, funext fun y => ?_⟩
    rw [tOp_apply hS w hϖ hu _ (Nat.lt_succ_iff.mp p.2.2) _ (Submodule.sum_mem _ fun i _ => hf2' _)]
    simp only [hv]
    exact Finset.sum_comm
  · rw [res, tOp_apply hS w hϖ hu j hj ψ hψ,
      hL E w r s ϖ hϖ hu j (fun g => ψ.1 (blk x y * finGL E _ (locGL E _ w g))) (fun X g => by
        obtain ⟨Y, hY⟩ := b2 X
        obtain ⟨Y', hY'⟩ := b3 x y Y
        simp only [map_mul]
        rw [hY, ← mul_assoc, hY', mul_assoc, hN])]
    simp only [b1, blk_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.OpComm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem hk_comm_of {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {K : Subgroup G} (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Hecke ℂ K) (A : Module.End ℂ V)
    (hA : ∀ g, Commute A (ρ g)) (x : V) : A (hkOp ρ hK hh x) = hkOp ρ hK hh (A x) :=
  map_heckeVec hK hh (ρ' := ρ) A (fun g y => LinearMap.congr_fun (hA g).eq y) x

theorem UpperTheory.V.Cj.S.opComm :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.OpComm := by
  intro hC E _ _ _ a T i i' φ hφ
  rcases i with ⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩ <;> rcases i' with ⟨t', u'⟩ | ⟨⟨w', hw'⟩, h', hh'⟩
  · exact LinearMap.congr_fun ((hC E a t u).2.2.2 t' u').eq φ
  · exact hk_comm_of (fL a w') (Final.GLintComm E w' a) hh' (cap t u) (fun g => (hC E a t u).1 _) φ
  · exact (hk_comm_of (fL a w) (Final.GLintComm E w a) hh (cap t' u') (fun g => (hC E a t' u').1 _) φ).symm
  · by_cases e : w = w'
    · subst e
      have hK := Final.GLintComm E w a
      change heckeVec (fL a w) (KGL w (n := a)) h (heckeVec (fL a w) (KGL w (n := a)) h' φ) =
        heckeVec (fL a w) (KGL w (n := a)) h' (heckeVec (fL a w) (KGL w (n := a)) h φ)
      rw [← SatCompare.heckeVec_conv hK hh hh' (hφ w hw), ← SatCompare.heckeVec_conv hK hh' hh (hφ w hw),
        Final.HeckeCommGL E w a ℂ h hh h' hh']
    · refine hk_comm_of (fL a w') (Final.GLintComm E w' a) hh' (hkOp (fL a w) (Final.GLintComm E w a) hh)
        (fun g => LinearMap.ext fun y => ?_) φ
      refine (hk_comm_of (fL a w) (Final.GLintComm E w a) hh (fL a w' g) (fun k => ?_) y).symm
      exact Commute.map (LocUniq.comm_locGL w (pLoc_locGL_of_ne e g) k) (finRep E a)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.PairEig
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem UpperTheory.V.Cj.S.eig_of_joint (hS : SatOfEig) (hC : CapOfEig)
    {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {T : Set (Pl E)} (hT : T.Finite)
    (φ : Sm E a) (h0 : φ ≠ 0) (haut : IsAutForm φ) (hfix : ∀ w ∉ T, φ ∈ fixed (fL a w) (KGL w (n := a)))
    (l : Ix a T → ℂ) (hl : ∀ i, opIx i φ = l i • φ) :
    ∃ (m : (E →+* ℂ) → Multiset ℂ) (B : Pl E → Multiset ℂˣ), Eig φ m B ∧
      (∀ t u, l (.inl (t, u)) = ((m t).map (u + ·)).prod) ∧
      ∀ (w : Pl E) (hw : w ∉ T) (ϖ : HeightOneSpectrum.adicCompletion E w) (hu : IsUnifV E w ϖ), ∀ j ≤ a,
        l (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩) = satEig (qV E w) a (B w) j := by
  classical
  obtain ⟨m, hm⟩ := hC E a φ h0 fun t u => ⟨_, hl (.inl (t, u))⟩
  have hB : ∀ w : Pl E, ∃ B : Multiset ℂˣ, w ∉ T → IsSatVecGL w (fL a w) φ B := by
    intro w
    by_cases hw : w ∈ T
    · exact ⟨0, fun h => (h hw).elim⟩
    · obtain ⟨B, hB⟩ := hS E w a _ (fL a w) φ h0 (hfix w hw) fun h hh => ⟨_, hl (.inr ⟨⟨w, hw⟩, ⟨h, hh⟩⟩)⟩
      exact ⟨B, fun _ => hB⟩
  choose B hB using hB
  refine ⟨m, B, ⟨h0, haut, hm, ?_⟩, fun t u => ?_, fun w hw ϖ hu j hj => ?_⟩
  · exact hT.eventually_cofinite_notMem.mono hB
  · exact smul_left_injective ℂ h0 ((hl (.inl (t, u))).symm.trans ((hm t).2 u))
  · exact smul_left_injective ℂ h0
      ((hl (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩)).symm.trans ((hB w hw).2.2.2 ϖ hu j hj))

theorem UpperTheory.V.Cj.S.pairEig :
    UpperTheory.V.Cj.S.TwoVar → UpperTheory.V.Cj.S.StabSp → UpperTheory.V.Cj.S.OpComm → UpperTheory.V.Cj.S.SatOfEig → UpperTheory.V.Cj.S.CapOfEig → UpperTheory.V.Cj.S.PairEig := by
  intro hTV hSt hOp hS hC E _ _ _ r s F S₁ S₂ b₁ b₂ hF h₁ h₂
  obtain ⟨T₁, hT₁, V₁, hS₁, fd₁, aut₁, fix₁, st₁⟩ := hSt E r S₁ b₁
  obtain ⟨T₂, hT₂, V₂, hS₂, fd₂, aut₂, fix₂, st₂⟩ := hSt E s S₂ b₂
  obtain ⟨φ₁, hφ₁, φ₂, hφ₂, l₁, l₂, n₁, n₂, e₁, e₂, H⟩ :=
    hTV _ _ (Sm E r) (Sm E s) V₁ V₂ fd₁ fd₂ (Ix r T₁) (Ix s T₂) opIx opIx st₁ st₂
      (fun i i' v hv => hOp E r T₁ i i' v fun w hw => fix₁ w hw hv)
      (fun i i' v hv => hOp E s T₂ i i' v fun w hw => fix₂ w hw hv) F hF
      (fun y => (h₁ y).imp fun f hf => ⟨hS₁ hf.1, hf.2⟩) (fun x => (h₂ x).imp fun f hf => ⟨hS₂ hf.1, hf.2⟩)
  obtain ⟨m₁, B₁, E₁, c₁, s₁⟩ := eig_of_joint hS hC hT₁ φ₁ n₁ (aut₁ _ hφ₁) (fun w hw => fix₁ w hw hφ₁) l₁ e₁
  obtain ⟨m₂, B₂, E₂, c₂, s₂⟩ := eig_of_joint hS hC hT₂ φ₂ n₂ (aut₂ _ hφ₂) (fun w hw => fix₂ w hw hφ₂) l₂ e₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, E₁, E₂, fun t u v G e hG he => ?_, ?_⟩
  · have := H Unit (fun _ => 1) (fun _ => .inl (t, u)) (fun _ => .inl (t, v)) (fun _ => G) e (fun _ => hG)
      (fun x y => by simpa using he x y)
    rw [← c₁, ← c₂]
    simpa using this
  · filter_upwards [hT₁.eventually_cofinite_notMem, hT₂.eventually_cofinite_notMem] with w hw₁ hw₂ ϖ hu c G e hG he
    have := H (Fin (r + 1) × Fin (s + 1)) c (fun p => .inr ⟨⟨w, hw₁⟩, ⟨_, Tj_mem_hecke hu p.1⟩⟩)
      (fun p => .inr ⟨⟨w, hw₂⟩, ⟨_, Tj_mem_hecke hu p.2⟩⟩) G e hG he
    rw [← this]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [s₁ w hw₁ ϖ hu p.1 (Nat.lt_succ_iff.1 p.1.2), s₂ w hw₂ ϖ hu p.2 (Nat.lt_succ_iff.1 p.2.2)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SatOfEig
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare GlobalTheory.LocGL GlobalTheory.WeylGL

namespace UpperTheory.V.Cj.S

theorem satOfEig : SatOfEig := by
  intro E _ _ w n V _ _ π x hx0 hx hsc
  have hK : IsCommensurated (KGL w (n := n)) := Final.GLintComm E w n
  obtain ⟨ϖ, hu⟩ := exists_isUnifV w
  have h0 := ne_zero_of_isUnifV hu
  choose c hc using fun j => hsc _ (Tj_mem_hecke (n := n) hu j)
  have c0 : c 0 = 1 := by
    have e : Tj ℂ n (Ov E w) ϖ 0 = dosetInd ℂ (KGL w (n := n)) 1 := by
      rw [Tj_eq h0]
      congr 1
    refine smul_left_injective ℂ hx0 ?_
    simp only [← hc 0, e, heckeVec_one hK hx, one_smul]
  have cn : c n ≠ 0 := by
    intro e
    have h1 := hc n
    have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w (n := n)) (tor h0 fun _ => 1) := by
      rw [Tj_eq h0]; simp
    rw [e, zero_smul, hTn, heckeVec_dosetInd (R := {tor h0 fun _ => 1}) hx, Finset.sum_singleton] at h1
    · exact hx0 (by simpa [← Module.End.mul_apply, ← map_mul] using congrArg (π (tor h0 fun _ => 1)⁻¹) h1)
    · intro γ hγ
      exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
    · intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
      refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
      rw [← tor_const_comm, mul_assoc, inv_mul_cancel_left]
      exact mul_mem ha hb
  obtain ⟨B, hB, hBc⟩ := _root_.GlobalTheory.LFun.exists_satEig_eq (qV E w) n (qV_ne_zero w) c c0 cn
  refine ⟨B, hx0, hx, hB, fun ϖ' hu' j hj => ?_⟩
  have hv : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, hu, hu', div_self WithZero.coe_ne_zero]
  have e := Final.TjIndep _ (Ov E w) ϖ (ϖ' / ϖ) ℂ n j hv.le
    (show Valued.v (ϖ' / ϖ)⁻¹ ≤ 1 by rw [map_inv₀, hv, inv_one]) (div_ne_zero (ne_zero_of_isUnifV hu') h0)
  rw [div_mul_cancel₀ _ h0] at e
  rw [e, hc j, hBc j hj]

end UpperTheory.V.Cj.S
end
end

