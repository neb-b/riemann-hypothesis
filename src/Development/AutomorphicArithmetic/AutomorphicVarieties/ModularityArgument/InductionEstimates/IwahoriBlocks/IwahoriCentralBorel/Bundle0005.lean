module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.FinIwa
section
section Par

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem unip_corner {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) :
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 ((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ 0 (1 : Matrix (Fin b) (Fin b) R) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Matrix.toBlocks₁₂, Fin.ext_iff] <;> omega

private theorem unip_any {a b : ℕ} {R : Type} [CommRing R] (B : Matrix (Fin a) (Fin b) R) : ∃ X : UPos (a + b) a → R,
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks 1 B 0 (1 : Matrix (Fin b) (Fin b) R) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 B 0 0) p.1.1 p.1.2, ?_⟩
  rw [unip_corner]
  congr 1
  ext i j
  have : (Fin.castAdd b i : Fin (a + b)) ≠ Fin.natAdd a j := by
    simp [Fin.ext_iff]; omega
  simp [unipMatrix, blockEntry_apply, Matrix.toBlocks₁₂, this]

private theorem split_par {a b : ℕ} {R : Type} [CommRing R] (g : GL (Fin (a + b)) R)
    (h : (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ (c : GL (Fin a) R) (d : GL (Fin b) R) (X : UPos (a + b) a → R), g = unipGL X * blk c d := by
  have e1 : g.val.submatrix finSumFinEquiv finSumFinEquiv * g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv =
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) := by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hg : ∀ M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R, g.val.submatrix finSumFinEquiv finSumFinEquiv = M →
      g.val = M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rintro _ rfl
    simp
  generalize g.val.submatrix finSumFinEquiv finSumFinEquiv = M at *
  generalize g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv = N at *
  have hM := (Matrix.fromBlocks_toBlocks M).symm
  rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, h, h', Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e1
  obtain ⟨e1, -, -, e2⟩ := e1
  obtain ⟨X, hX⟩ := unip_any (M.toBlocks₁₂ * N.toBlocks₂₂)
  refine ⟨⟨_, _, e1, mul_eq_one_comm.1 e1⟩, ⟨_, _, e2, mul_eq_one_comm.1 e2⟩, X, Units.ext ?_⟩
  have hX' : unipMatrix X = (Matrix.fromBlocks 1 (M.toBlocks₁₂ * N.toBlocks₂₂) 0 1).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hX]; simp
  rw [Units.val_mul, coe_unipGL, hX', hg M rfl]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_assoc, mul_eq_one_comm.1 e2, Matrix.mul_one]
  rw [← h, ← hM]

private theorem par_of_low {K : Type} [Field K] [NumberField K] (s : G1 K (2 + 2))
    (h : ((s : AdelicGLn.AdelicGL K (2 + 2)).val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : ((s : AdelicGLn.AdelicGL K (2 + 2))⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ X m₁ m₂ t, s = nn X * lv m₁ m₂ t := by
  obtain ⟨hlv, -, -, -, hdet, -⟩ := blkLaws (K := K)
  obtain ⟨a, d, X, hX⟩ := split_par (s : AdelicGLn.AdelicGL K (2 + 2)) h h'
  refine ⟨X, retractOne a, retractOne d, Real.log (detModule K 2 a).1, ?_⟩
  have h1 : detModule K 2 a * detModule K 2 d = 1 := by
    have := mem_normOneGL_iff_detModule.1 s.2
    rwa [hX, map_mul, mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL _), one_mul, hdet] at this
  have z1 : zt K (Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 a) := by
    unfold zt
    congr 1
    exact Subtype.ext (Real.exp_log (detModule K 2 a).2)
  have z2 : zt K (-Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 d) := by
    unfold zt
    congr 1
    refine Subtype.ext ?_
    rw [eq_inv_of_mul_eq_one_right h1]
    show Real.exp (-Real.log _) = _
    rw [Real.exp_neg, Real.exp_log (detModule K 2 a).2]
    rfl
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, hlv, z1, z2, coe_retractOne, coe_retractOne, inv_mul_cancel_right, inv_mul_cancel_right]
  exact hX

private theorem low_of_borel {K : Type} [Field K] [NumberField K] {b : AdelicGLn.AdelicGL K (2 + 2)} (hb : b ∈ adelicBorel) :
    (b.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
  ext i j
  refine mem_adelicBorel.1 hb ?_
  show finSumFinEquiv (Sum.inl j) < finSumFinEquiv (Sum.inr i)
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

end Par

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical NumberField.AdeleRing

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem snd_entry (x : AdelicGLn.FiniteAdelicGL K n) (a b : Fin n) :
    ((finEmb K n x : AdelicGLn.AdelicGL K n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd K n (finEmb K n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

private theorem cf_snd (v : Pl K) (x : AdelicGLn.AdelicGL K n) : GM.cf v (AdelicGLn.prodEquiv K n x).2 = finAt v x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb K n (AdelicGLn.prodEquiv K n x).2 : AdelicGLn.AdelicGL K n) a b).2 v = (x a b).2 v
  rw [snd_entry, AdelicGLn.prodEquiv_apply_snd]

private theorem cf_mul (v : Pl K) (x y : AdelicGLn.FiniteAdelicGL K n) : GM.cf v (x * y) = GM.cf v x * GM.cf v y := by
  unfold GM.cf
  rw [map_mul, finAt_mul]

private theorem central_borel (s : {r : ℝ // 0 < r}) : centralSection K n s ∈ adelicBorel := by
  refine mem_adelicBorel.2 ?_
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]
  exact Matrix.blockTriangular_diagonal _

private theorem fin_borel (y : AdelicGLn.FiniteAdelicGL K n)
    (hy : ∀ v : Pl K, ∀ i j : Fin n, j < i → GM.cf v y i j = 0) : finEmb K n y ∈ adelicBorel := by
  refine mem_adelicBorel.2 fun i j hij => ?_
  have hij' : j < i := hij
  refine adele_ext (fun w => ?_) fun v => ?_
  · have e1 : (finEmb K n y i j).1 = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j :=
      congrArg (fun z => z.1 i j) (prodEquiv_finEmb y)
    rw [e1, Matrix.one_apply_ne hij'.ne']
    rfl
  · exact hy v i j hij'

private theorem proj_borel (y : AdelicGLn.FiniteAdelicGL K n) (h : finEmb K n y ∈ adelicBorel) :
    (MultiplicityOne.finProj K n y : AdelicGLn.AdelicGL K n) ∈ adelicBorel := by
  rw [MultiplicityOne.coe_finProj]
  exact mul_mem h (inv_mem (central_borel _))

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.finIwa :
    ∀ {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ (h : FA K (2 + 2)) (k : archCompact K (2 + 2)), ∃ X m₁ m₂ t g u, (∀ U, u ∈ levOn (im w) U) ∧
        arc1 k * fin1 h = nn X * lv m₁ m₂ t * arc1 k * fin1 (ι₄ g) * fin1 u := by
  intro K _ _ r w ι hw hι h k
  obtain ⟨-, -, hoff, hdec, hcomm, -⟩ := (embEx (K := K) (2 + 2) w hw).2 ι hι
  obtain ⟨b, hb, c, hc, e⟩ := exists_adelicBorel_mul_maxCompact (finEmb K (2 + 2) h)
  have hh : h = (AdelicGLn.prodEquiv K (2 + 2) b).2 * (AdelicGLn.prodEquiv K (2 + 2) c).2 := by
    have := congrArg (fun x => (AdelicGLn.prodEquiv K (2 + 2) x).2) e
    simpa [prodEquiv_finEmb, map_mul] using this
  obtain ⟨g₁, b', eb, hb'⟩ := hdec (AdelicGLn.prodEquiv K (2 + 2) b).2
  obtain ⟨g₂, u, eu, hu⟩ := hdec (AdelicGLn.prodEquiv K (2 + 2) c).2
  have hcb : ι g₂ * b' = b' * ι g₂ := (hcomm g₂ b' hb').eq
  have hh2 : h = ι (g₁ * g₂) * b' * u := by
    rw [hh, eb, eu, map_mul, mul_assoc (ι g₁), ← mul_assoc b', ← hcb]
    simp only [mul_assoc]

  have hb1 : ∀ v ∉ im w, GM.cf v b' = finAt v b := fun v hv => by
    rw [← cf_snd, eb, cf_mul, hoff g₁ v hv, one_mul]
  have hu1 : ∀ v ∉ im w, GM.cf v u = finAt v c := fun v hv => by
    rw [← cf_snd, eu, cf_mul, hoff g₂ v hv, one_mul]
  have hup : finEmb K (2 + 2) b' ∈ adelicBorel := by
    refine fin_borel b' fun v i j hij => ?_
    by_cases hv : v ∈ im w
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hb' l]
      exact Matrix.one_apply_ne hij.ne'
    · rw [hb1 v hv]
      change (b i j).2 v = 0
      rw [mem_adelicBorel.1 hb hij]
      rfl
  have hs := proj_borel b' hup
  obtain ⟨X, m₁, m₂, t, hX⟩ := par_of_low (fin1 b') (low_of_borel hs) (low_of_borel (inv_mem hs))
  refine ⟨X, m₁, m₂, t, g₁ * g₂, u, fun U v => ?_, ?_⟩
  · by_cases hv : v ∈ im w
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      beta_reduce
      rw [if_pos hv]
      change GM.cf (w l) u ∈ U (w l)
      rw [hu l]
      exact one_mem _
    · beta_reduce
      rw [if_neg hv]
      change GM.cf v u ∈ _
      rw [hu1 v hv]
      exact hc.2 v
  · have c1 : Commute (arc1 k) (fin1 b') := (levLaws (K := K) (2 + 2) (im w)).2.2.1 k b'
    have c2 : fin1 (ι (g₁ * g₂)) * fin1 b' = fin1 b' * fin1 (ι (g₁ * g₂)) := by
      rw [← map_mul, ← map_mul, (hcomm (g₁ * g₂) b' hb').eq]
    have e3 : fin1 (ι (g₁ * g₂) * b' * u) = fin1 (ι (g₁ * g₂)) * fin1 b' * fin1 u :=
      (map_mul _ _ _).trans (congrArg (· * fin1 u) (map_mul _ _ _))
    rw [← hX, hh2, e3, c2, ← c1.eq]
    simp only [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HopEmb
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem cosets_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W : Subgroup G}
    (hW : CO W) (g : G) : {c : G ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)}.Finite := by
  haveI : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hW.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ W) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hW.1.image hc).finite_of_discrete).subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.hopEmb :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) {r : ℕ} (w : Fin r → Pl K) (ι : GS n w →* FA K n), Function.Injective w → IsEmb w ι → ∀ U, Lev U → ∀ φ : G1 K n → ℂ, FixF (levOn (im w) U) φ →
      ∀ g, hop (levOn (im w) U) (ι g) φ = hopR (rS ι) (Subgroup.pi Set.univ fun i => U (w i)) g φ := by
  intro K _ _ n r w ι hw hι U hU φ hφ g
  obtain ⟨hcf, hoff, -, hcomm, hmem⟩ := ((embEx n w hw).2 ι hι).2
  have hcf' : ∀ (v : Pl K), GM.cf v (1 : FA K n) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    intro v
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      have := hcf 1 i
      rw [map_one] at this
      rw [this]
      exact Subgroup.one_mem _
    · have := hoff 1 v hv
      rw [map_one] at this
      rw [this]
      exact Subgroup.one_mem _
  have hcf1 : ∀ i, GM.cf (w i) (1 : FA K n) = 1 := by
    intro i
    have := hcf 1 i
    rwa [map_one] at this
  set L := levOn (im w) U with hL
  set W : Subgroup (GS n w) := Subgroup.pi Set.univ fun i => U (w i) with hWdef
  have hWL : ∀ a ∈ W, ι a ∈ L := fun a ha =>
    (hmem U _).2 ⟨a, 1, (mul_one _).symm, fun i => ha i trivial, hcf1, hcf'⟩
  have hLW : ∀ x, ι x ∈ L → x ∈ W := by
    intro x hx
    obtain ⟨a, h', e, ha, h1, -⟩ := (hmem U _).1 hx
    have e' : h' = ι (a⁻¹ * x) := by rw [map_mul, map_inv, e, inv_mul_cancel_left]
    have e1 : a⁻¹ * x = 1 := funext fun i => by
      rw [← hcf (a⁻¹ * x) i, ← e', h1]
      rfl
    rw [(inv_mul_eq_one.1 e1).symm]
    exact fun i _ => ha i
  have hW : CO W :=
    ⟨isCompact_univ_pi fun j => (hU (w j)).1.1, isOpen_set_pi Set.finite_univ fun j _ => (hU (w j)).1.2⟩
  let e : GS n w ⧸ W → FA K n ⧸ L := fun c => QuotientGroup.mk (ι c.out)
  have he : ∀ y, e (QuotientGroup.mk y) = QuotientGroup.mk (ι y) := by
    intro y
    refine QuotientGroup.eq.2 ?_
    have := hWL _ (QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk y : GS n w ⧸ W)))
    rwa [map_mul, map_inv] at this
  have hbij : Set.BijOn e {c : GS n w ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)}
      {c : FA K n ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * ι g)} := by
    refine ⟨?_, ?_, ?_⟩
    · rintro c ⟨u, hu, rfl⟩
      exact ⟨ι u, hWL u hu, by rw [he, map_mul]⟩
    · intro c _ d _ hcd
      have h1 := QuotientGroup.eq.1 hcd
      rw [← map_inv, ← map_mul] at h1
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
      exact QuotientGroup.eq.2 (hLW _ h1)
    · rintro c ⟨u, hu, rfl⟩
      obtain ⟨a, h', e', ha, h1, h2⟩ := (hmem U _).1 hu
      have hh' : h' ∈ L := (hmem U _).2 ⟨1, h', by simp, fun i => Subgroup.one_mem _, h1, h2⟩
      refine ⟨QuotientGroup.mk (a * g), ⟨a, fun i _ => ha i, rfl⟩, ?_⟩
      rw [he, map_mul, e']
      refine QuotientGroup.eq.2 ?_
      have : (ι a * ι g)⁻¹ * (ι a * h' * ι g) = h' := by
        rw [mul_assoc (ι a) h', (hcomm g h' h1).symm.eq]
        group
      rwa [this]
  have hfin := cosets_finite hW g
  funext x
  have hR : hopR (rS ι) W g φ x = ∑ᶠ c ∈ {c : GS n w ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)}, φ (x * fin1 (ι c.out)) := by
    unfold hopR
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_apply]
    rfl
  rw [hR]
  unfold hop
  symm
  refine finsum_mem_eq_of_bijOn e hbij fun c _ => ?_
  have hl : (ι c.out)⁻¹ * (e c).out ∈ L := QuotientGroup.eq.1 (QuotientGroup.out_eq' (e c)).symm
  have := hφ _ hl (x * fin1 (ι c.out))
  rw [← this, mul_assoc, ← map_mul, mul_inv_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevBlock
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}

private theorem bval (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (PositivityTheory.Rg.Tf.Adel.blk x y).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val 0 0 y.val) := rfl

private def bHom : GL (Fin a) R × GL (Fin b) R →* GL (Fin (a + b)) R where
  toFun p := PositivityTheory.Rg.Tf.Adel.blk p.1 p.2
  map_one' := by
    apply Units.ext
    simp only [bval, Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.fromBlocks_one, Matrix.reindex_apply,
      Matrix.submatrix_one_equiv]
  map_mul' p q := by
    apply Units.ext
    simp only [Units.val_mul, Prod.fst_mul, Prod.snd_mul, bval, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem bHom_map (f : R →+* S) (x : GL (Fin a) R) (y : GL (Fin b) R) :
    Matrix.GeneralLinearGroup.map f (bHom (x, y)) =
      bHom (Matrix.GeneralLinearGroup.map f x, Matrix.GeneralLinearGroup.map f y) := by
  apply Units.ext
  ext i j
  change f ((PositivityTheory.Rg.Tf.Adel.blk x y).val i j) = (PositivityTheory.Rg.Tf.Adel.blk _ _).val i j
  simp only [bval, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

private theorem bHom_cont [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (bHom : GL (Fin a) R × GL (Fin b) R → GL (Fin (a + b)) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

private theorem bHom_ent (O : Subring S) (x : GL (Fin a) S) (y : GL (Fin b) S) (hx : ∀ i j, x i j ∈ O)
    (hy : ∀ i j, y i j ∈ O) (i j : Fin (a + b)) : bHom (x, y) i j ∈ O := by
  change (PositivityTheory.Rg.Tf.Adel.blk x y).val i j ∈ O
  simp only [bval, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [hx, hy]

end SlopeTestRemainingChoices

section Glob

variable {K : Type} [Field K] [NumberField K] {a b : ℕ}

private theorem bHom_int (v : Pl K) {x : Gw a v} {y : Gw b v} (hx : x ∈ GLnLocal.integralGL (v.adicCompletion K) a)
    (hy : y ∈ GLnLocal.integralGL (v.adicCompletion K) b) :
    bHom (x, y) ∈ GLnLocal.integralGL (v.adicCompletion K) (a + b) := by
  rw [GLnLocal.mem_integralGL_iff, ← map_inv]
  have h1 := (GLnLocal.mem_integralGL_iff _ _).1 hx
  have h2 := (GLnLocal.mem_integralGL_iff _ _).1 hy
  exact ⟨bHom_ent _ _ _ h1.1 h2.1, bHom_ent _ _ _ h1.2 h2.2⟩

private theorem finAt_bHom (v : Pl K) (x : AdelicGLn.AdelicGL K a) (y : AdelicGLn.AdelicGL K b) :
    finAt v (bHom (x, y)) = bHom (finAt v x, finAt v y) :=
  bHom_map (finEval v) x y

private theorem finEmb_bHom (x : FA K a) (y : FA K b) :
    finEmb K (a + b) (bHom (x, y)) = bHom (finEmb K a x, finEmb K b y) := by
  apply (AdelicGLn.prodEquiv K (a + b)).injective
  rw [prodEquiv_finEmb]
  have e1 : ∀ {c : ℕ} (p : AdelicGLn.AdelicGL K c), (AdelicGLn.prodEquiv K c p).1 =
      Matrix.GeneralLinearGroup.map (show AdeleRing (𝓞 K) K →+* InfiniteAdeleRing K from RingHom.fst _ _) p :=
    fun p => Units.ext (Matrix.ext fun _ _ => rfl)
  have e2 : ∀ {c : ℕ} (p : AdelicGLn.AdelicGL K c), (AdelicGLn.prodEquiv K c p).2 =
      Matrix.GeneralLinearGroup.map (show AdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 K) K from RingHom.snd _ _) p :=
    fun p => Units.ext (Matrix.ext fun _ _ => rfl)
  have h1 : ∀ (p : AdelicGLn.AdelicGL K a) (q : AdelicGLn.AdelicGL K b),
      (AdelicGLn.prodEquiv K (a + b) (bHom (p, q))).1 =
        bHom ((AdelicGLn.prodEquiv K a p).1, (AdelicGLn.prodEquiv K b q).1) := by
    intro p q
    rw [e1, e1, e1, bHom_map]
  have h2 : ∀ (p : AdelicGLn.AdelicGL K a) (q : AdelicGLn.AdelicGL K b),
      (AdelicGLn.prodEquiv K (a + b) (bHom (p, q))).2 =
        bHom ((AdelicGLn.prodEquiv K a p).2, (AdelicGLn.prodEquiv K b q).2) := by
    intro p q
    rw [e2, e2, e2, bHom_map]
  refine Prod.ext ?_ ?_
  · rw [h1, prodEquiv_finEmb, prodEquiv_finEmb]
    exact (map_one bHom).symm
  · rw [h2, prodEquiv_finEmb, prodEquiv_finEmb]

private theorem coe_finite_adele_inclusion {n : ℕ} {u : FA K n} (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    ((fin1 u : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n u :=
  congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hu)))

private theorem zt0 : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

end Glob

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levBlock :
    ∀ {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v), Lev U → ∀ g, ∃ U₂ : ∀ v : Pl K, Subgroup (Gw 2 v), Lev U₂ ∧ ∀ u₁ ∈ levOn (im w) U₂, ∀ u₂ ∈ levOn (im w) U₂,
        ∃ u ∈ levOn (im w) U, ∀ k : archCompact K (2 + 2), lv (fin1 u₁) (fin1 u₂) 0 * arc1 k * fin1 (ι₄ g) = arc1 k * fin1 (ι₄ g) * fin1 u := by
  intro K _ _ r w ι hw hι U hU g
  obtain ⟨h4, -, hcomm, -, -, hconj⟩ := levLaws (K := K) (2 + 2) (im w)
  obtain ⟨U', hU', hc⟩ := hconj w ι hw hι rfl U hU g
  let U₂ : ∀ v : Pl K, Subgroup (Gw 2 v) := fun v =>
    GLnLocal.integralGL (v.adicCompletion K) 2 ⊓
      ((U' v).comap (bHom.comp (MonoidHom.inl _ _)) ⊓ (U' v).comap (bHom.comp (MonoidHom.inr _ _)))
  have hU₂ : Lev U₂ := by
    intro v
    have ho : IsOpen (U₂ v : Set (Gw 2 v)) :=
      (GLnLocal.isOpen_integralGL _ _).inter
        (((hU' v).1.2.preimage (bHom_cont.comp (continuous_id.prodMk continuous_const))).inter
          ((hU' v).1.2.preimage (bHom_cont.comp (continuous_const.prodMk continuous_id))))
    exact ⟨⟨(GLnLocal.isCompact_integralGL _ _).of_isClosed_subset ((U₂ v).isClosed_of_isOpen ho)
      (fun x hx => hx.1), ho⟩, inf_le_left⟩
  refine ⟨U₂, hU₂, fun u₁ h₁ u₂ h₂ => ?_⟩
  have hm : bHom (u₁, u₂) ∈ levOn (im w) U' := by
    intro v
    have e₁ := h₁ v
    have e₂ := h₂ v
    rw [finEmb_bHom, finAt_bHom]
    by_cases hv : v ∈ im w
    · simp only [hv, if_true] at e₁ e₂ ⊢
      have := (U' v).mul_mem e₁.2.1 e₂.2.2
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul] at this
      simpa using this
    · simp only [hv, if_false] at e₁ e₂ ⊢
      exact bHom_int v e₁ e₂
  have hl : lv (fin1 u₁) (fin1 u₂) 0 = fin1 (bHom (u₁, u₂)) := by
    have h2 := ((levLaws (K := K) 2 (im w)).1 U₂ hU₂).2
    apply Subtype.ext
    rw [blkLaws.1, neg_zero, zt0, mul_one, mul_one, coe_finite_adele_inclusion (h2 h₁), coe_finite_adele_inclusion (h2 h₂), coe_finite_adele_inclusion ((h4 U' hU').2 hm),
      finEmb_bHom]
    rfl
  refine ⟨_, hc _ hm, fun k => ?_⟩
  rw [hl, ← (hcomm k _).eq, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
  congr 2
  group
end

