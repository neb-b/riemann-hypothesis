module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import GroundTheory.GlobalFields.IdeleGroups.UnitBound
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
public import GroundTheory.AutomorphicForms.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem lf_fin {K : Type} [Field K] [NumberField K] {S : Set 𝔸[K]} (hS : IsCompact S) :
    {k : K | algebraMap K 𝔸[K] k ∈ S}.Finite := by
  have h1 := GroundTheory.Global.discreteTopology_principalSubgroup K
  have h2 := GroundTheory.Global.isClosed_principalSubgroup K
  have h3 : IsCompact ((Subtype.val : NumberField.AdeleRing.principalSubgroup (𝓞 K) K → 𝔸[K]) ⁻¹' S) :=
    h2.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  have h4 := h3.finite_of_discrete
  refine Set.Finite.of_finite_image (f := algebraMap K 𝔸[K]) ((h4.image Subtype.val).subset ?_)
    (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K).injOn
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨⟨_, k, rfl⟩, hk, rfl⟩

private theorem lf_ray (K : Type) [Field K] [NumberField K] (T : ℝ) :
    ∃ Z : Set 𝔸[K], IsCompact Z ∧ ∀ t, T ≤ t →
      ((zt K (-t) : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) 𝔸[K]).det ∈ Z := by
  set e : ℝ := (((2 : ℕ) : ℝ) * Module.finrank ℚ K)⁻¹ with he
  have he0 : 0 ≤ e := by positivity
  let B : Set (InfiniteAdeleRing K) :=
    Set.univ.pi fun w : InfinitePlace K => Metric.closedBall (0 : w.Completion) (Real.exp (-T) ^ e)
  have hB : IsCompact B := isCompact_univ_pi fun w => isCompact_closedBall _ _
  let Z0 : Set 𝔸[K] := B ×ˢ ({1} : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
  have hZ0 : IsCompact Z0 := hB.prod isCompact_singleton
  refine ⟨(fun x => x * x) '' Z0, hZ0.image (continuous_id.mul continuous_id), fun t ht => ?_⟩
  have hp : 0 < Real.exp (-t) ^ e := Real.rpow_pos_of_pos (Real.exp_pos _) e
  refine ⟨(posIdele (K := K) _ hp : GroundTheory.Global.IdeleGroup K), ⟨fun w _ => ?_, ?_⟩, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_posIdele_infinite]
    exact Real.rpow_le_rpow (Real.exp_pos _).le (Real.exp_le_exp.2 (by linarith)) he0
  · exact DFunLike.ext _ _ fun v => posIdele_finite _ hp v
  · rw [← AdelicGLn.coe_det]
    have : zt K (-t) = diagUnits 2 fun _ => posIdele (K := K) _ hp := rfl
    rw [this, det_diagUnits, Fin.prod_univ_two, Units.val_mul]

private theorem lf_minor {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R)
    (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (c : Fin 2 → Fin (2 + 2)) :
    ((unipMatrix X * (blk a b).val * h).submatrix (Fin.natAdd 2) c).det =
      b.val.det * (h.submatrix (Fin.natAdd 2) c).det := by
  rw [← Matrix.det_mul]
  congr 1
  ext i j
  have h1 : ∀ (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (k : Fin (2 + 2)),
      (unipMatrix X * M) (Fin.natAdd 2 i) k = M (Fin.natAdd 2 i) k := by
    intro M k
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro l _
    rw [blockEntry_apply, dite_eq_right, zero_mul]
    simp
  rw [Matrix.submatrix_apply, mul_assoc, h1, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.locFin :
    ∀ {K : Type} [Field K] [NumberField K] (C : Set (G1 K (2 + 2))) (T : ℝ), IsCompact C → {q : Cos K | ∃ g ∈ C, T ≤ HH ((q.out : G1 K (2 + 2)) * g)}.Finite := by
  intro K _ _ C T hC
  obtain ⟨D, hD, -, hxD⟩ := GroundTheory.Global.IdeleGroup.exists_isCompact_normOneSubgroup K
  obtain ⟨Z, hZ, hzZ⟩ := lf_ray K T
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 _).1
  let mn : (Fin 2 → Fin (2 + 2)) → G1 K (2 + 2) → 𝔸[K] := fun c g =>
    (((g : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det
  have hmn : ∀ c, Continuous (mn c) := fun c =>
    ((Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _).matrix_det
  let Φ : (Fin 2 → Fin (2 + 2)) → GroundTheory.Global.IdeleGroup K × 𝔸[K] × G1 K (2 + 2) × G1 K (2 + 2) → 𝔸[K] :=
    fun c p => (p.1 : 𝔸[K]) * p.2.1 * mn c (p.2.2.1 * p.2.2.2⁻¹)
  have hΦ : ∀ c, Continuous (Φ c) := fun c =>
    ((Units.continuous_val.comp continuous_fst).mul continuous_snd.fst).mul
      ((hmn c).comp (continuous_snd.snd.fst.mul continuous_snd.snd.snd.inv))
  have hfin : ∀ c, {k : K | algebraMap K 𝔸[K] k ∈ Φ c '' (D ×ˢ Z ×ˢ (KG K (2 + 2) : Set (G1 K (2 + 2))) ×ˢ C)}.Finite :=
    fun c => lf_fin ((hD.prod (hZ.prod (hK.prod hC))).image (hΦ c))
  have hrat : ∀ q : Cos K, ∃ γ : GL (Fin (2 + 2)) K, AdelicGLn.diagonal K (2 + 2) γ =
      ((q.out : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := fun q => q.out.2
  choose γ hγ using hrat
  have hm : ∀ q c, mn c (q.out : G1 K (2 + 2)) =
      algebraMap K 𝔸[K] ((γ q : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det := by
    intro q c
    simp only [mn]
    rw [← hγ, RingHom.map_det]
    rfl
  have key : ∀ q : Cos K, (∃ g ∈ C, T ≤ HH ((q.out : G1 K (2 + 2)) * g)) → ∃ a : Kˣ, ∀ c,
      algebraMap K 𝔸[K] (a * ((γ q : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det) ∈
        Φ c '' (D ×ˢ Z ×ˢ (KG K (2 + 2) : Set (G1 K (2 + 2))) ×ˢ C) := by
    rintro q ⟨g, hg, hT⟩
    obtain ⟨X, m₁, m₂, t, k, hk, hq⟩ := iwa ((q.out : G1 K (2 + 2)) * g)
    rw [hq, (hpSpec (K := K)).1, ((hpSpec (K := K)).2.1 k hk).1, add_zero] at hT
    have hm2 : AdelicGLn.det K 2 (m₂ : AdelicGLn.AdelicGL K 2) ∈ GroundTheory.Global.IdeleGroup.normOneSubgroup K :=
      mem_normOneGL_iff_detModule.1 m₂.2
    obtain ⟨a, ha⟩ := hxD _ hm2
    refine ⟨a, fun c => ⟨⟨_, ((zt K (-t) : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) 𝔸[K]).det, k, g⟩, ⟨ha, hzZ t hT, hk, hg⟩, ?_⟩⟩
    have hq' : (q.out : G1 K (2 + 2)) = nn X * lv m₁ m₂ t * (k * g⁻¹) := by
      rw [← mul_assoc, ← hq, mul_inv_cancel_right]
    rw [map_mul, ← hm, hq']
    simp only [Φ, mn]
    rw [Subgroup.coe_mul _ (nn X * _), Subgroup.coe_mul _ (nn X), (blkLaws (K := K)).1, Units.val_mul (_ * blk _ _),
      Units.val_mul _ (blk _ _), coe_unipOne, coe_unipGL, lf_minor, Units.val_mul, Units.val_mul (m₂ : AdelicGLn.AdelicGL K 2),
      Matrix.det_mul, GroundTheory.Global.IdeleGroup.coe_diagonal, AdelicGLn.coe_det]
    ring
  choose! a ha using key
  refine Set.Finite.of_finite_image
    (f := fun q c => (a q : K) * ((γ q : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det)
    ((Set.Finite.pi' hfin).subset ?_) ?_
  · rintro _ ⟨q, hq, rfl⟩ c
    exact ha q hq c
  · intro q _ q' _ h
    have h1 := (pluck (γ q') (γ q)).2 (((a q')⁻¹ * a q : Kˣ) : K) fun c => by
      have := congrFun h c
      simp only at this
      rw [Units.val_mul, mul_assoc, this, ← mul_assoc, Units.inv_mul, one_mul]
    rw [← q.out_eq, ← q'.out_eq]
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    rw [(pkLaws (K := K)).1]
    intro i j hi hj
    have h2 : (((q'.out * q.out⁻¹ : Gam K (2 + 2)) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
        AdelicGLn.diagonal K (2 + 2) (γ q' * (γ q)⁻¹) := by
      rw [map_mul, map_inv, hγ, hγ]; rfl
    rw [h2]
    have h3 := AdelicGLn.diagonal_apply K (2 + 2) (γ q' * (γ q)⁻¹) i j
    rw [h1 i j hi hj, map_zero] at h3
    exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LongCell
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem lc_inv_compact {K : Type} [Field K] [NumberField K] {B : Set 𝔸[K]} (hB : IsCompact B) {a : ℝ} (ha : 0 < a) :
    ∃ T : Set 𝔸[K], IsCompact T ∧ ∀ u : GroundTheory.Global.IdeleGroup K, (u : 𝔸[K]) ∈ B →
      a ≤ (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) → (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) ≤ 1 →
      ((u⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) ∈ T := by
  obtain ⟨S, hS, hc⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := K) ha 1
  have hci : Continuous fun s : GroundTheory.Global.IdeleGroup K => ((s⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) :=
    Units.continuous_coe_inv
  have hE : IsCompact ((fun p : 𝔸[K] × GroundTheory.Global.IdeleGroup K => p.1 * ((p.2⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K])) '' (B ×ˢ S)) :=
    (hB.prod hS).image (continuous_fst.mul (hci.comp continuous_snd))
  haveI := GroundTheory.Global.t2Space_adeleRing K
  haveI := GroundTheory.Global.discreteTopology_principalSubgroup K
  have hF := ((GroundTheory.Global.isClosed_principalSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hE).finite_of_discrete
  have hF2 := hF.image (fun x : AdeleRing.principalSubgroup (𝓞 K) K => Ring.inverse (x : 𝔸[K]))
  refine ⟨_, (hF2.isCompact.prod hS).image (f := fun p : 𝔸[K] × GroundTheory.Global.IdeleGroup K =>
    p.1 * ((p.2⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K])) (continuous_fst.mul (hci.comp continuous_snd)), fun u hu h1 h2 => ?_⟩
  obtain ⟨c, hcS⟩ := hc u h1 h2
  set d := GroundTheory.Global.IdeleGroup.diagonal K c with hd
  have hmem : ((d⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) ∈ AdeleRing.principalSubgroup (𝓞 K) K := by
    rw [hd, ← map_inv]
    exact ⟨((c⁻¹ : Kˣ) : K), rfl⟩
  refine ⟨((d : 𝔸[K]), d * u), ⟨⟨⟨_, hmem⟩, ⟨((u : 𝔸[K]), d * u), ⟨hu, hcS⟩, ?_⟩, ?_⟩, hcS⟩, ?_⟩
  · change (u : 𝔸[K]) * _ = _
    rw [← Units.val_mul, mul_inv_rev, mul_inv_cancel_left]
  · change Ring.inverse ((d⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) = _
    rw [Ring.inverse_unit, inv_inv]
  · change (d : 𝔸[K]) * _ = _
    rw [← Units.val_mul, mul_inv, mul_inv_cancel_left]

private theorem lc_rows {R : Type} [CommRing R] (X Y : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) (k : GL (Fin (2 + 2)) R)
    (h : wGL R * unipGL X = unipGL Y * blk a b * k) :
    b.val * k.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) = 1 ∧
      ∀ (i j : Fin 2) (hp), X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), hp⟩ =
        (b.val * k.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2)) i j := by
  have hL : ∀ (i : Fin 2) (j : Fin (2 + 2)), (wGL R * unipGL X).val (Fin.natAdd 2 i) j = unipMatrix X (Fin.castAdd 2 i) j := by
    intro i j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [wGL, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, coe_unipGL, Matrix.one_apply, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hU : ∀ (i : Fin 2) (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (j : Fin (2 + 2)),
      (unipMatrix Y * M) (Fin.natAdd 2 i) j = M (Fin.natAdd 2 i) j := by
    intro i M j
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro l _
    rw [blockEntry_apply, dite_eq_right (by simp), zero_mul]
  have hR : ∀ (i : Fin 2) (j : Fin (2 + 2)), (unipGL Y * blk a b * k).val (Fin.natAdd 2 i) j =
      ∑ l, b.val i l * k.val (Fin.natAdd 2 l) j := by
    intro i j
    rw [mul_assoc, Units.val_mul, coe_unipGL, hU, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add]
  have key : ∀ (i : Fin 2) (j : Fin (2 + 2)), ∑ l, b.val i l * k.val (Fin.natAdd 2 l) j = unipMatrix X (Fin.castAdd 2 i) j :=
    fun i j => by rw [← hL, h, hR]
  refine ⟨?_, fun i j hp => ?_⟩
  · ext i j
    rw [Matrix.mul_apply]
    refine (key i (Fin.castAdd 2 j)).trans ?_
    rw [unipMatrix, Matrix.add_apply, blockEntry_apply, dite_eq_right (fun hh => absurd hh.2 (not_le.2 j.2)), add_zero]
    simp [Matrix.one_apply, Fin.ext_iff]
  · rw [Matrix.mul_apply]
    refine Eq.trans ?_ (key i (Fin.natAdd 2 j)).symm
    rw [unipMatrix, Matrix.add_apply, blockEntry_apply, dite_eq_left hp, Matrix.one_apply_ne, zero_add]
    intro e
    have := congrArg Fin.val e
    simp at this
    omega

private theorem lc_adj {R : Type} [CommRing R] (b c : Matrix (Fin 2) (Fin 2) R) (h : b * c = 1) :
    b = b.det • c.adjugate := by
  have h1 : c.adjugate = c.det • b := by
    have := congrArg (· * c.adjugate) h
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul] at this
    exact this.symm
  rw [h1, smul_smul, ← Matrix.det_mul, h, Matrix.det_one, one_smul]

private theorem lc_main {K : Type} [Field K] [NumberField K] (X : UPos (2 + 2) 2 → 𝔸[K]) (k : G1 K (2 + 2)) (hk : k ∈ KG K (2 + 2)) :
    ∃ (b : AdelicGLn.AdelicGL K 2), ∃ k' ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))),
      (detModule K 2 b⁻¹).1 = Real.exp (HH (w0 K * unipOne (K := K) (n := 2 + 2) 2 X * k)) ∧
      (detModule K 2 b⁻¹).1 ≤ 1 ∧
      b.val * k'.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) = 1 ∧
      ∀ (i j : Fin 2) (hp), X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), hp⟩ =
        (b.val * k'.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2)) i j := by
  obtain ⟨Y, m₁, m₂, t, k', hk', e⟩ := iwa (w0 K * unipOne (K := K) (n := 2 + 2) 2 X)
  obtain ⟨h1, h2, -⟩ := hpSpec (K := K)
  obtain ⟨b1, -, -, -, -, -, b2, -⟩ := blkLaws (K := K)
  have hH : HH (w0 K * unipOne (K := K) (n := 2 + 2) 2 X * k) = t := by
    rw [(h2 k hk).2, e, h1, (h2 k' hk').1, add_zero]
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, b1, b2, coe_unipOne] at e'
  obtain ⟨r1, r2⟩ := lc_rows X Y _ _ _ e'
  refine ⟨(m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t), k', hk', ?_, ?_, r1, r2⟩
  · rw [hH, map_inv, map_mul, mem_normOneGL_iff_detModule.1 m₂.2, one_mul, zt, detModule_centralSection two_pos]
    change (Real.exp (-t))⁻¹ = _
    rw [Real.exp_neg, inv_inv]
  · have hs := subDet (2 + 2) (k' : AdelicGLn.AdelicGL K (2 + 2)) hk' (Fin.natAdd 2) (Fin.castAdd 2)
      (Fin.natAdd_injective 2 2) (Fin.castAdd_injective 2 2)
    exact hs.2.2 _ (Units.inv_eq_of_mul_eq_one_right r1)

private noncomputable def lcF {K : Type} [Field K] [NumberField K] (q : 𝔸[K] × AdelicGLn.AdelicGL K (2 + 2)) (p : UPos (2 + 2) 2) : 𝔸[K] :=
  q.1 * ((q.2.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2)).adjugate * q.2.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2))
    ⟨(p.1.1 : ℕ), p.2.1⟩ ⟨(p.1.2 : ℕ) - 2, by have := p.1.2.2; omega⟩

private theorem continuous_lower_left_block {K : Type} [Field K] [NumberField K] :
    Continuous fun k : AdelicGLn.AdelicGL K (2 + 2) => k.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) :=
  Units.continuous_val.matrix_submatrix _ _

private theorem continuous_lower_right_block {K : Type} [Field K] [NumberField K] :
    Continuous fun k : AdelicGLn.AdelicGL K (2 + 2) => k.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2) :=
  Units.continuous_val.matrix_submatrix _ _

private theorem lc_cont {K : Type} [Field K] [NumberField K] : Continuous (lcF (K := K)) := by
  refine continuous_pi fun p => ?_
  unfold lcF
  exact continuous_fst.mul (((continuous_lower_left_block.matrix_adjugate.matrix_mul continuous_lower_right_block).matrix_elem _ _).comp continuous_snd)

private theorem lc_eq {K : Type} [Field K] [NumberField K] (X : UPos (2 + 2) 2 → 𝔸[K]) (b : Matrix (Fin 2) (Fin 2) 𝔸[K])
    (k' : AdelicGLn.AdelicGL K (2 + 2)) (h3 : b * k'.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) = 1)
    (h4 : ∀ (i j : Fin 2) (hp), X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), hp⟩ =
        (b * k'.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2)) i j) : X = lcF (b.det, k') := by
  funext p
  obtain ⟨⟨i, j⟩, hi, hj⟩ := p
  have hj2 := j.2
  have hi' : (i : ℕ) < 2 := hi
  have hj' : 2 ≤ (j : ℕ) := hj
  obtain ⟨i, rfl⟩ : ∃ i' : Fin 2, i = Fin.castAdd 2 i' := ⟨⟨i, hi'⟩, Fin.ext rfl⟩
  obtain ⟨j, rfl⟩ : ∃ j' : Fin 2, j = Fin.natAdd 2 j' := ⟨⟨(j : ℕ) - 2, by omega⟩, Fin.ext (by simp; omega)⟩
  have hb := lc_adj _ _ h3
  rw [h4 i j]
  conv_lhs => rw [hb]
  rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  simp [lcF]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.longCell :
    ∀ {K : Type} [Field K] [NumberField K],
      (∀ (X : UPos (2 + 2) 2 → 𝔸[K]), ∀ k ∈ KG K (2 + 2),
        HH (w0 K * unipOne (K := K) (n := 2 + 2) 2 X * k) ≤ 0) ∧
      ∀ R : ℝ, ∃ C : Set (UPos (2 + 2) 2 → 𝔸[K]), IsCompact C ∧ ∀ X, ∀ k ∈ KG K (2 + 2),
        -R ≤ HH (w0 K * unipOne (K := K) (n := 2 + 2) 2 X * k) → X ∈ C := by
  intro K _ _
  refine ⟨fun X k hk => ?_, fun R => ?_⟩
  · obtain ⟨b, k', -, h1, h2, -⟩ := lc_main X k hk
    rw [h1] at h2
    exact Real.exp_le_one_iff.1 h2
  have hB : IsCompact ((fun k : AdelicGLn.AdelicGL K (2 + 2) => (k.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2)).det) ''
      (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2)))) :=
    (isCompact_maxCompact (K := K) (n := 2 + 2)).image continuous_lower_left_block.matrix_det
  obtain ⟨T, hT, hu⟩ := lc_inv_compact hB (Real.exp_pos (-R))
  refine ⟨lcF '' (T ×ˢ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2)))),
    (hT.prod (isCompact_maxCompact (K := K) (n := 2 + 2))).image lc_cont, fun X k hk hR => ?_⟩
  obtain ⟨b, k', hk', h1, h2, h3, h4⟩ := lc_main X k hk
  have hinv : ((b⁻¹ : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) 𝔸[K]) = k'.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) :=
    Units.inv_eq_of_mul_eq_one_right h3
  have hmem : ((AdelicGLn.det K 2 b : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) ∈ T := by
    have h5 := hu (AdelicGLn.det K 2 b⁻¹) ⟨k', hk', by rw [AdelicGLn.coe_det, hinv]⟩
      ((Real.exp_le_exp.2 hR).trans h1.ge) h2
    rwa [← map_inv, inv_inv] at h5
  rw [AdelicGLn.coe_det] at hmem
  exact ⟨(_, k'), ⟨hmem, hk'⟩, (lc_eq X b.val k' h3 h4).symm⟩
end

