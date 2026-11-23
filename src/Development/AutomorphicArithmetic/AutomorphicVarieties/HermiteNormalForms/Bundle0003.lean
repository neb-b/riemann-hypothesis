module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Psdcone
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.psdcone :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), IsClosed (Psd L N) ∧ (∀ c : ℝ, 0 < c → ∀ k ∈ Psd L N, c • k ∈ Psd L N) ∧
    Pos L N ⊆ Psd L N ∧ (ConeExtensionAcyclic.posDual (Psd L N)).Nonempty := by
  intro L _ _ N
  have hc : ∀ (w : InfinitePlace L) (i j : Fin N), Continuous (fun h : HS L N => mat h w i j) := by
    intro w i j
    exact (continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp continuous_subtype_val))
  have htr : ∀ k ∈ Psd L N, ∀ w, 0 ≤ (mat k w).trace := by
    intro k hk w
    exact Finset.sum_nonneg fun i _ => (hk w).diag_nonneg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hP : Psd L N = ⋂ w : InfinitePlace L, ⋂ x : Fin N →₀ ℂ,
        {h : HS L N | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * mat h w i j * xj} := by
      ext h
      simp only [Psd, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hh w x
        exact (hh w).2 x
      · intro hh w
        exact ⟨mat_herm h w, hh w⟩
    rw [hP]
    refine isClosed_iInter fun w => isClosed_iInter fun x => ?_
    refine isClosed_le continuous_const ?_
    unfold Finsupp.sum
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (hc w i j)).mul continuous_const
  · intro c hc k hk w
    show (mat (c • k) w).PosSemidef
    rw [mat_smul]
    exact (hk w).smul hc.le
  · intro k hk w
    exact (hk w).posSemidef
  · let f : HS L N →ₗ[ℝ] ℝ :=
      { toFun := fun h => ∑ w, ((mat h w).trace).re
        map_add' := by
          intro h k
          simp only [← Finset.sum_add_distrib, ← Complex.add_re, ← Matrix.trace_add]
          rfl
        map_smul' := by
          intro c h
          simp only [mat_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          simp }
    have hf : Continuous f := by
      show Continuous (fun h : HS L N => ∑ w, ((mat h w).trace).re)
      exact continuous_finsetSum _ fun w _ =>
        Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => hc w i i)
    refine ⟨⟨f, hf⟩, ?_⟩
    intro k hk hk0
    have hw : ∃ w, mat k w ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hk0 (HS_ext fun w => by rw [hne w, mat_zero])
    obtain ⟨w, hw⟩ := hw
    show 0 < ∑ w, ((mat k w).trace).re
    have hpos : 0 < ((mat k w).trace).re := by
      have h1 : 0 ≤ (mat k w).trace := htr k hk w
      have h2 : (mat k w).trace ≠ 0 := fun h0 => hw (((hk w).trace_eq_zero_iff).mp h0)
      exact (Complex.lt_def.mp (lt_of_le_of_ne h1 (Ne.symm h2))).1
    refine lt_of_lt_of_le hpos ?_
    refine Finset.single_le_sum (f := fun w => ((mat k w).trace).re) (fun v _ => ?_) (Finset.mem_univ w)
    exact (Complex.le_def.mp (htr k hk v)).1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rankhs
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.rankhs :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ), Module.finrank ℝ (HS L N) ≤ dd L N * N := by
  intro L _ _ _ N
  refine (Submodule.finrank_le (HSsub L N)).trans (le_of_eq ?_)
  have h1 := IsTotallyComplex.finrank L
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces L
  have h3 := IsTotallyComplex.nrRealPlaces_eq_zero L
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, dd]
  rw [h1, h2, h3]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.RealVec
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.gramq :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), (gram h).IsHermitian ∧
    (∀ x : Fin N × BI L → ℝ, x ⬝ᵥ (gram h *ᵥ x) = qR h (realVec x)) ∧
    (∀ c : Fin N × BI L → ℤ, realVec (fun s => (c s : ℝ)) = toR (intVec c)) ∧
    Function.Bijective (intVec : (Fin N × BI L → ℤ) → Lat L N) := by
  intro L _ _ N h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun s t => ?_
    simp only [gram, of_apply, star_trivial]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← (mat_herm h w).apply t.1 s.1]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  · intro x
    have key : ∀ w, (star (realVec x w) ⬝ᵥ mat h w *ᵥ realVec x w).re =
        ∑ s, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) := by
      intro w
      have hr : ∀ s t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) =
          ((x s : ℂ) * (star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)) * (x t : ℂ)).re := by
        intro s t
        rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul]
        ring
      simp only [hr, ← Complex.re_sum]
      congr 1
      simp only [realVec, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', Complex.star_def,
        Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Eq.trans ?_ Finset.sum_comm.symm
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Eq.trans ?_ Finset.sum_comm.symm
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [qR, key]
    simp only [dotProduct, mulVec, gram, of_apply, Finset.mul_sum, Finset.sum_mul]
    calc ∑ s, ∑ t, ∑ w, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t)
        = ∑ s, ∑ w, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  · intro c
    funext w a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [realVec, toR, intVec, map_sum, zsmul_eq_mul]
  · let E : (Fin N × BI L → ℤ) ≃ Lat L N :=
      (Equiv.curry _ _ _).trans
        (Equiv.piCongrRight fun _ => (RingOfIntegers.basis L).equivFun.symm.toEquiv)
    have hE : (intVec : (Fin N × BI L → ℤ) → Lat L N) = E := by
      funext c a
      simp [E, intVec, Module.Basis.equivFun_symm_apply, Equiv.curry]
    rw [hE]
    exact E.bijective
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Realsurj
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

open NumberField.InfinitePlace in
private theorem one_coord (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L]
    (z : InfinitePlace L → ℂ) :
    ∃ x : BI L → ℝ, ∀ w, ∑ i, (x i : ℂ) * embO w (RingOfIntegers.basis L i) = z w := by
  classical
  let m : mixedEmbedding.mixedSpace L := (0, fun w => z w.1)
  let c := (mixedEmbedding.latticeBasis L).repr m
  refine ⟨fun i => c i, fun w => ?_⟩
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  have hsum := (mixedEmbedding.latticeBasis L).sum_repr m
  have h2 := congrArg (fun p : mixedEmbedding.mixedSpace L => p.2 ⟨w, hw⟩) hsum
  simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
    mixedEmbedding.latticeBasis_apply, mixedEmbedding.mixedEmbedding_apply_isComplex,
    integralBasis_apply, Complex.real_smul, m] at h2
  rw [← h2]
  rfl

theorem UpperTheory.V.KT.realsurj :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ),
    Function.Surjective (realVec : (Fin N × BI L → ℝ) → VR L N) := by
  intro L _ _ _ N z
  choose x hx using fun a : Fin N => one_coord L (fun w => z w a)
  exact ⟨fun s => x s.1 s.2, funext fun w => funext fun a => hx a w⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.RynePlace
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem ryne_place (L : Type) [Field L] [NumberField L] (x : 𝓞 L) (hx : x ≠ 0) :
    ∃ w : InfinitePlace L, 1 ≤ w (x : L) := by
  classical
  by_contra hc
  push_neg at hc
  have hprod := InfinitePlace.prod_eq_abs_norm (x : L)
  rw [← Algebra.coe_norm_int] at hprod
  have hn : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  have h1 : (1 : ℝ) ≤ ((|((Algebra.norm ℤ x : ℤ) : ℚ)| : ℚ) : ℝ) := by
    have := Int.one_le_abs hn
    rw [← Int.cast_abs]
    exact_mod_cast this
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have hf : ∀ w : InfinitePlace L, 0 ≤ w (x : L) ^ w.mult := fun w => by positivity
  have hlt : ∀ w : InfinitePlace L, w (x : L) ^ w.mult < 1 := fun w =>
    pow_lt_one₀ (by positivity) (hc w) InfinitePlace.mult_pos.ne'
  have hle : ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult ≤ 1 :=
    Finset.prod_le_one₀ (fun w _ => hf w) (fun w _ => (hlt w).le)
  have : ∏ w : InfinitePlace L, w (x : L) ^ w.mult < 1 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w0)]
    calc w0 (x : L) ^ w0.mult * ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult
        ≤ w0 (x : L) ^ w0.mult * 1 := mul_le_mul_of_nonneg_left hle (hf w0)
      _ < 1 := by rw [mul_one]; exact hlt w0
  linarith

theorem UpperTheory.V.KT.ryne :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), (Ry L N).Nonempty := by
  intro L _ _ N
  refine ⟨mkHS (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ => isHermitian_one), ?_⟩
  intro y hy
  have hterm : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (funext hc)
  obtain ⟨w, hw⟩ := ryne_place L (y a) ha
  have hw' : ‖embO w (y a)‖ = w ((y a : 𝓞 L) : L) := by
    simp only [embO, RingHom.comp_apply]
    exact InfinitePlace.norm_embedding_eq w _
  simp only [q, qR, mat_mkHS, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum, hterm, toR]
  calc (1 : ℝ) ≤ ‖embO w (y a)‖ ^ 2 := by rw [hw']; nlinarith
    _ ≤ ∑ a', ‖embO w (y a')‖ ^ 2 :=
      Finset.single_le_sum (f := fun a' => ‖embO w (y a')‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ a)
    _ ≤ ∑ w', ∑ a', ‖embO w' (y a')‖ ^ 2 :=
      Finset.single_le_sum (f := fun w' => ∑ a', ‖embO w' (y a')‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ w)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Scinv
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.scinv :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (A : Matrix (Fin N) (Fin N) (𝓞 L)), A.det ≠ 0 →
    0 < nrmDet A ∧ ∃ B : Matrix (Fin N) (Fin N) (𝓞 L), A * B = ((nrmDet A : ℕ) : 𝓞 L) • (1 : Matrix (Fin N) (Fin N) (𝓞 L)) ∧
      B * A = ((nrmDet A : ℕ) : 𝓞 L) • (1 : Matrix (Fin N) (Fin N) (𝓞 L)) := by
  intro L _ _ N A hA
  refine ⟨Int.natAbs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hA), ?_⟩
  have hmem : ((Ideal.absNorm (Ideal.span {A.det}) : ℕ) : 𝓞 L) ∈ Ideal.span {A.det} :=
    Ideal.absNorm_mem _
  rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' : ((nrmDet A : ℕ) : 𝓞 L) = A.det * c := hc
  refine ⟨c • A.adjugate, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc', mul_comm]
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hc', mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Spanpsd
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.spanpsd :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Set (Lat L N)),
    (∀ k ∈ Psd L N, (∀ y ∈ M, q k y = 0) → k = 0) → Spans M := by
  intro L _ _ N M hM
  classical
  by_contra hS
  have hlt : spanL M < ⊤ := lt_top_iff_ne_top.mpr hS
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  set c : Fin N → L := fun i => f (fun j => if i = j then 1 else 0) with hcdef
  have hfc : ∀ x : Fin N → L, f x = ∑ i, x i * c i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ]
    rfl
  have hc0 : ∃ i, c i ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [hfc]
    simp [hc]
  obtain ⟨i0, hi0⟩ := hc0
  let u : InfinitePlace L → Fin N → ℂ := fun w i => w.embedding (c i)
  let A : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ := fun w => vecMulVec (star (u w)) (u w)
  have hA : ∀ w, (A w).PosSemidef := fun w => posSemidef_vecMulVec_star_self (u w)
  let k : HS L N := mkHS A (fun w => (hA w).isHermitian)
  have hmat : ∀ w, mat k w = A w := fun w => rfl
  have hkP : k ∈ Psd L N := by
    intro w
    rw [hmat]
    exact hA w
  have hq : ∀ y ∈ M, q k y = 0 := by
    intro y hy
    have hyk : f (toL y) = 0 := hker (Submodule.subset_span ⟨y, hy, rfl⟩)
    rw [hfc] at hyk
    show ∑ w, (star (toR y w) ⬝ᵥ mat k w *ᵥ toR y w).re = 0
    refine Finset.sum_eq_zero fun w _ => ?_
    have hsum : ∑ j, u w j * toR y w j = 0 := by
      have : w.embedding (∑ j, toL y j * c j) = 0 := by rw [hyk, map_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_comm]
      rfl
    have hAz : mat k w *ᵥ toR y w = 0 := by
      funext i
      rw [hmat]
      simp only [A, mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum, hsum,
        mul_zero, Pi.zero_apply]
    rw [hAz]
    simp
  have hk0 := hM k hkP hq
  have w0 : InfinitePlace L := Classical.arbitrary _
  have h1 : mat k w0 i0 i0 = 0 := by
    rw [hk0]
    rfl
  rw [hmat] at h1
  simp only [A, vecMulVec_apply, Pi.star_apply, u] at h1
  have hne : w0.embedding (c i0) ≠ 0 := (map_ne_zero _).mpr hi0
  exact hne (by
    rcases mul_eq_zero.mp h1 with h | h
    · exact star_eq_zero.mp h
    · exact h)
end

