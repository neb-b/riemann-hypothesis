module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.KFinOfMem
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.CommuteOfUnitaryConjugate
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def jE (n : ℕ) (ε : ℤˣ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := Matrix.fromBlocks 0 1 (((ε : ℤ) : ℂ) • 1) 0

def thB (d : SD σ) (ε : ℤˣ) (w : InfinitePlace F) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ :=
  d.b.1.map (d.B.emb w).1 * (jE d.n ε)ᵀ * (d.b⁻¹).1.map (d.B.emb w).1

def thA {d : SD σ} (R : RD d) (w : InfinitePlace F) : Matrix (Fin d.m) (Fin d.m) ℂ :=
  (-(Complex.I * ((((R.ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * R.ζ))) • 1

theorem map_incM' {w : InfinitePlace F} (τ : EmbOver E w) {ι ι' : Type} (J : Matrix ι ι' E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (GlobalTheory.CompanionTheory.CMAdele.piInf_tmul τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

theorem map_star_mul' {ι : Type} [Fintype ι] (x y : Matrix ι ι ℂ) : (x * y).map star = x.map star * y.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem commute_of_unitary_conjugate {ι : Type} [Fintype ι] [DecidableEq ι] {bw biw kw M Dw J : Matrix ι ι ℂ} (e1 : bw * biw = 1)
    (e2 : biw * bw = 1) (hMk : M = biw * kw * bw) (hu : M * Mᴴ = 1) (hJ : bwᵀ * Dw * bw.map star = J)
    (hk2 : kwᵀ * Dw * kw.map star = Dw) : Commute kw (bw * Jᵀ * biw) := by
  have hMJ : Mᵀ * J * M.map star = J := by
    rw [← hJ, hMk]
    simp only [Matrix.transpose_mul, map_star_mul']
    have e1' : bw.map star * biw.map star = 1 := by
      rw [← map_star_mul', e1]; ext i j; simp [Matrix.one_apply, apply_ite]
    have e1t : biwᵀ * bwᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    calc _ = bwᵀ * kwᵀ * (biwᵀ * bwᵀ) * Dw * (bw.map star * biw.map star) * kw.map star * bw.map star := by
          simp only [Matrix.mul_assoc]
      _ = bwᵀ * (kwᵀ * Dw * kw.map star) * bw.map star := by
          rw [e1t, e1']; simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      _ = bwᵀ * Dw * bw.map star := by rw [hk2]
  have hc1 : M.map star * Mᵀ = 1 := by
    have : M.map star * Mᵀ = (M * Mᴴ)ᵀ := by rw [Matrix.transpose_mul]; rfl
    rw [this, hu, Matrix.transpose_one]
  have hcomm : Mᵀ * J = J * Mᵀ := by
    calc Mᵀ * J = Mᵀ * J * (M.map star * Mᵀ) := by rw [hc1, Matrix.mul_one]
      _ = (Mᵀ * J * M.map star) * Mᵀ := by simp only [Matrix.mul_assoc]
      _ = J * Mᵀ := by rw [hMJ]
  have hcomm' : Jᵀ * M = M * Jᵀ := by
    have := congrArg Matrix.transpose hcomm
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using this
  have hkw : kw = bw * M * biw := by
    rw [hMk]; simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]; rw [Matrix.mul_assoc, e1, Matrix.mul_one]
  show kw * (bw * Jᵀ * biw) = bw * Jᵀ * biw * kw
  rw [hkw]
  calc bw * M * biw * (bw * Jᵀ * biw) = bw * (M * (biw * bw) * Jᵀ) * biw := by
        simp only [Matrix.mul_assoc]
    _ = bw * (Jᵀ * M) * biw := by rw [e2, Matrix.mul_one, hcomm']
    _ = bw * Jᵀ * biw * (bw * M * biw) := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc biw bw, e2, Matrix.one_mul]

theorem commute_thB {d : SD σ} (R : RD d) {k : d.G} (hk : k ∈ d.K) (w : InfinitePlace F) :
    Commute ((mat2 k).map (piInf (d.B.emb w))) (thB d R.ε w) := by
  have h := d.ok.good.cm
  have e1 : d.b.1.map (d.B.emb w).1 * (d.b⁻¹).1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMk : (inFrame d.b k).map (piInf (d.B.emb w)) =
      (d.b⁻¹).1.map (d.B.emb w).1 * (mat2 k).map (piInf (d.B.emb w)) * d.b.1.map (d.B.emb w).1 := by
    rw [inFrame, Matrix.map_mul, Matrix.map_mul, map_incM', map_incM']
  have hu := ((d.ok.stdK k).1 hk).1 w
  have cst : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E, (x.map σ).map (d.B.emb w).1 =
      (x.map (d.B.emb w).1).map star := fun x => by
    ext i j; exact h.2.2.2 (d.B.emb w).1 (x i j)
  have cstA : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E),
      (x.map (cA σ)).map (piInf (d.B.emb w)) = (x.map (piInf (d.B.emb w))).map star :=
    fun x => by ext i j; exact GlobalTheory.ThK.Dbl.Dense.piInf_cA h (d.B.emb w) (x i j)
  have hDw : (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) = (dbl d.Y.J).map (d.B.emb w).1 := by
    rw [← map_incM']
    congr 1
    ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]
  have hJ : (d.b.1.map (d.B.emb w).1)ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) *
      (d.b.1.map (d.B.emb w).1).map star = jE d.n R.ε := by
    have := congrArg (fun x => x.map (d.B.emb w).1) R.hε
    simp only [Matrix.map_mul, Matrix.transpose_map, cst] at this
    rw [hDw, this]
    ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [jE, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, hij]
  have hk2 : ((mat2 k).map (piInf (d.B.emb w)))ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) *
      ((mat2 k).map (piInf (d.B.emb w))).map star = (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) := by
    have hk0 : (k.1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
        (k.1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J) := k.2
    have := congrArg (fun x => x.map (piInf (d.B.emb w))) hk0
    simp only [Matrix.map_mul, Matrix.transpose_map, cstA] at this
    exact this
  exact commute_of_unitary_conjugate e1 e2 hMk hu hJ hk2

end PositivityTheory.SiegelWeilFormula.KK

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.IsCompactK
section
noncomputable section

attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCompact_K (d : SD σ) : IsCompact (d.K : Set d.G) := by
  have hB := d.ok.good
  have hK := d.ok.stdK
  obtain ⟨Φ, hΦ, eΦ⟩ := GlobalTheory.ThK.Dbl.St.exists_section hB.cm d.B.emb
  have hI : IsCompact (intHat F E : Set (AE F E)) := SiegelEisensteinSeries.BRoad.isCompact_intHat
  have hfe : finOne F = GlobalTheory.ThK.Dbl.St.eF F := rfl
  set T : Set (AE F E) := Φ '' Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1) + (intHat F E : Set (AE F E))
    with hTdef
  have hT : IsCompact T := ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).image hΦ).add hI
  have hentry : ∀ k ∈ d.K, ∀ i j, inFrame d.b k i j ∈ T := by
    intro k hk i j
    obtain ⟨h1, h2⟩ := (hK k).1 hk
    rw [eΦ (inFrame d.b k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      have hu : (inFrame d.b k).map (piInf (d.B.emb w)) ∈ Matrix.unitaryGroup (Fin d.n ⊕ Fin d.n) ℂ :=
        Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose]; exact h1 w)
      exact entry_norm_bound_of_unitary hu i j
    · rw [← hfe]
      exact h2 k (Set.mem_insert _ _) i j
  set S : Set (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :=
    (fun M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) => incM F d.b.1 * M * incM F (d.b⁻¹).1) ''
      Set.univ.pi (fun _ => Set.univ.pi fun _ => T) with hSdef
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hT).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  have hmat : ∀ k ∈ d.K, mat2 k ∈ S := fun k hk => ⟨inFrame d.b k, fun i _ j _ => hentry k hk i j, by
    show incM F d.b.1 * (incM F (d.b⁻¹).1 * mat2 k * incM F d.b.1) * incM F (d.b⁻¹).1 = mat2 k
    simp only [Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.one_mul]⟩
  have hp : ∀ w, Continuous (piInf (d.B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (d.B.emb w)
  have hIc := hI.isClosed
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := d.Y) d.b
  have hKset : (d.K : Set d.G) =
      (⋂ w, {k | (inFrame d.b k).map (piInf (d.B.emb w)) * ((inFrame d.b k).map (piInf (d.B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, {k : d.G | finOne F • inFrame d.b k i j ∈ intHat F E}) ∩
          (⋂ i, ⋂ j, {k : d.G | finOne F • inFrame d.b k⁻¹ i j ∈ intHat F E})) := by
    ext k
    simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.forall_mem_insert,
      Set.mem_singleton_iff, forall_eq]
  have hKc : IsClosed (d.K : Set d.G) := by
    rw [hKset]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_))
    · exact (hfr.matrix_map (hp w)).matrix_mul (hfr.matrix_map (hp w)).matrix_conjTranspose
    · exact (hfr.matrix_elem i j).const_smul (finOne F)
    · exact ((hfr.comp continuous_inv).matrix_elem i j).const_smul (finOne F)
  exact GlobalTheory.ThK.Dbl.St.isCompact_of_units (UG (cA σ) (dbl (incM F d.Y.J))) (GlobalTheory.EisBL.DoubledGroupTopology.isClosed_doubled_group σ d.Y) d.K hKc S hS
    fun k hk => ⟨hmat k hk, hmat k⁻¹ (d.K.inv_mem hk)⟩

end PositivityTheory.SiegelWeilFormula.KK

end
end

