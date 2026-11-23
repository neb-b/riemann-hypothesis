module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BrCusp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AbsHarm
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem absHarm_real {z : ℂ} (h : z = starRingEnd ℂ z) (h0 : z.re = 0) : z = 0 := by
  have h1 := congrArg Complex.im h
  rw [Complex.conj_im] at h1
  exact Complex.ext h0 (by rw [Complex.zero_im]; linarith)

theorem UpperTheory.V.Lit.Bor.absHarm :
    UpperTheory.V.Lit.Bor.AbsHarm := by
  intro E _ _ _ a n e he M _ _ _ _ A B hA hB hAB hc H hH hadj q ω hω
  have hadj' := fun q ω η => ipAdj E a n e M (A + B) (B - A) H ⊤ (fun X x _ y _ => hadj X x y) q ω η
    (fun _ => Submodule.mem_top) (fun _ => Submodule.mem_top)
  have hdef := ipDef E a n e he M H ⊤ hH
  have hpos := fun q ω => ((hdef q).2 ω (fun _ => Submodule.mem_top)).1
  have hzero := fun q ω (h : (ip e H ω ω).re = 0) =>
    ((hdef q).2 ω (fun _ => Submodule.mem_top)).2 (absHarm_real ((hdef q).1 ω ω) h)
  have hc0 : cas B e - cas A e = 0 := sub_eq_zero.2 hc
  cases q with
  | zero =>
    refine ⟨hzero _ _ ?_, trivial⟩
    have h1 := kugaZero E a n e M A B hAB ω hω
    have h2 : ip e H (del (B - A) e (dCo (A + B) ω)) ω = 0 := by
      simp only [ip, h1, hc0, LinearMap.zero_apply, map_zero, Finset.sum_const_zero]
    rw [hadj', h2, mul_zero, Complex.zero_re]
  | succ q =>
    have h1 := kugaSucc E a n e he M A B hA hB hAB q ω hω
    have h2 : ip e H (dCo (A + B) (del (B - A) e ω)) ω + ip e H (del (B - A) e (dCo (A + B) ω)) ω = 0 := by
      simp only [ip]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun I _ => ?_
      rw [← LinearMap.add_apply, ← map_add (f := _), h1, hc0, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
    have h3 := congrArg Complex.re (hadj' (q + 1) (dCo (A + B) ω) ω)
    have h4 := congrArg Complex.re (hadj' q ω (del (B - A) e ω))
    have h5 := congrArg Complex.re ((hdef (q + 1)).1 ω (dCo (A + B) (del (B - A) e ω)))
    have h6 := congrArg Complex.re h2
    have p1 := hpos _ (dCo (A + B) ω)
    have p2 := hpos _ (del (B - A) e ω)
    rw [Complex.conj_re] at h5
    rw [Complex.add_re, Complex.zero_re] at h6
    have hmul : ∀ (k : ℕ) (z : ℂ), (((k : ℂ) + 1) * z).re = ((k : ℝ) + 1) * z.re := fun k z => by simp
    rw [hmul] at h3 h4
    have q0 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    have q1 : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) + 1 := by positivity
    have h7 : (ip e H (dCo (A + B) ω) (dCo (A + B) ω)).re +
        (((q + 1 : ℕ) : ℝ) + 1) * ((q : ℝ) + 1) * (ip e H (del (B - A) e ω) (del (B - A) e ω)).re = 0 := by
      rw [h3, mul_assoc, ← h4, ← h5, ← mul_add, add_comm (Complex.re _), h6, mul_zero]
    have p3 := mul_nonneg (mul_pos q1 q0).le p2
    refine ⟨hzero _ _ (by linarith), hzero _ _ ?_⟩
    exact (mul_eq_zero.1 (show _ * _ = (0 : ℝ) from le_antisymm (by linarith) p3)).resolve_left (mul_pos q1 q0).ne'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasXi
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.casXi :
    UpperTheory.V.Lit.Bor.CasXi := by
  intro E _ _ _ a n e he Ξ r
  obtain ⟨h1, h2⟩ := UpperTheory.V.Lit.Bor.xiSchur E a Ξ
  have h3 : IsLieHom (shift Ξ.dmat r) := (UpperTheory.V.Lit.Bor.ellFacts E a).2.2.2 _ _ r h1
  refine h2 _ fun X => ?_
  have h4 := UpperTheory.V.Lit.Bor.casComm E a n e he _ _ h3 X
  rw [shift_apply] at h4
  have h5 : Commute (cas (shift Ξ.dmat r) e) ((r * ell E a X) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)) :=
    (Commute.one_right _).smul_right _
  simpa using h4.sub_right h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasZero
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.casZero :
    UpperTheory.V.Lit.Bor.CasZero := by
  intro E _ _ _ a n e he M _ _ _ _ κ A B hA hB hAB hκ hinf c hc hcoh
  by_contra hne
  have hdel : ∀ (q : ℕ) (X : Fin q → Herm E a),
      del (B - A) e (0 : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M) X = 0 := fun q X => by
    rw [del_apply]
    simp
  rcases hcoh with ⟨ω, hco, hcl, hnz⟩ | ⟨q, ω, hco, hcl, hne'⟩
  · apply hnz
    ext X
    have h := kugaZero E a n e M A B hAB ω (hinf 0 ω hco) X
    rw [hcl, hdel, hc] at h
    exact (smul_eq_zero.1 h.symm).resolve_left hne
  · have hδ := delCochain E a n e he M κ (B - A) hκ q ω hco
    let s : M →ₗ[ℝ] M := (c⁻¹ • LinearMap.id : M →ₗ[ℂ] M).restrictScalars ℝ
    have hs : ∀ X, s.compAlternatingMap (del (B - A) e ω) X = c⁻¹ • del (B - A) e ω X := fun X => rfl
    refine hne' (s.compAlternatingMap (del (B - A) e ω)) (fun k X => ?_) (AlternatingMap.ext fun X => ?_)
    · rw [hs, hs, map_smul, hδ k X]
    · have h := kugaSucc E a n e he M A B hA hB hAB q ω (hinf _ ω hco) X
      rw [hcl, hdel, add_zero, hc, dCo_apply] at h
      have h2 : ω X = c⁻¹ • (c • ω X) := (inv_smul_smul₀ hne _).symm
      rw [dCo_apply, h2, ← h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hs, map_smul, smul_comm c⁻¹]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CuspSq
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

open MeasureTheory GlobalTheory.UnitaryBC in
open scoped GlobalTheory.CuspRep.CuspidalL2GL in
private theorem isSqInt_of_cusp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {ψ : Sm E a}
    (hψ : IsCuspForm ψ) (hn : ∀ t g, ψ.1 (splitCentre E a t * g) = ψ.1 g) : IsSqInt ψ.1 := by
  classical
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (GA E a), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  have := (GlobalTheory.CovolGL.finvol E a μ).1
  have hc : Continuous ψ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E a ψ hψ.1.level
  obtain ⟨C, hC⟩ := (UpperTheory.V.KernelIndexFullLattice.partC UpperTheory.V.KernelIndexFullLattice.splitEq_holds UpperTheory.V.KernelIndexFullLattice.brCusp_holds E a ψ hψ
    (fun t g => by rw [hn t g]))
  exact (GlobalTheory.CuspRep.CuspidalL2GL.memL2_iff_isSqInt (μ := μ) hc hψ.1.left hn).1
    (GlobalTheory.CuspQuot.memL2_of_bound (μ := μ) hc (GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL hψ.1.left hn) hC)

theorem UpperTheory.V.Lit.Bor.cuspSq :
    UpperTheory.V.Lit.Bor.CuspSq := by
  intro E _ _ _ a ha π r hr φ hφ
  obtain ⟨χ, ⟨s, hs⟩, hχ⟩ := UpperTheory.V.Lit.Bor.twEx E a ha r
  have key : ∀ ψ ∈ π.V, IsSqIntMod ψ := fun ψ hψ => by
    have h0 : lie E a (oneL E a) (mulChi a χ ψ) = (0 : ℂ) • mulChi a χ ψ := by
      rw [hχ, hr ψ hψ, (UpperTheory.V.Lit.Bor.ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, zero_smul,
        map_zero]
    have h1 := isSqInt_of_cusp ((π.cusp ψ hψ).mulChi χ) fun t g => by
      rw [UpperTheory.V.Lit.Bor.aInv E a _ 0 h0 t g, zero_mul, Complex.exp_zero, one_mul]
    refine ⟨s, χ, hs, ?_⟩
    have e : (fun g => ((chiDet a χ g : ℂˣ) : ℂ) * ψ.1 g) = (mulChi a χ ψ).1 := funext fun g => by
      rw [mulChi_apply, mul_comm]
    rw [e]
    exact h1
  refine ⟨(π.cusp φ hφ).1.left, (π.cusp φ hφ).1.level, hr φ hφ, fun l => key _ ?_⟩
  induction l with
  | nil => exact hφ
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons]
    exact π.stable (.lie X) _ ih
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CxGrpComp
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cxGrp_comp {T : Type} [Fintype T] {a : ℕ} {Φ : (Fin a → Fin a → T → ℂ) → ℂ}
    (hΦ : DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)}) (g h : GL (Fin a) (T → ℂ)) :
    DifferentiableOn ℂ (fun x : Fin a → Fin a → T → ℂ => Φ (fun i j => (g.val * Matrix.of x * h.val) i j))
      {x | IsUnit (Matrix.of x)} := by
  have hd : Differentiable ℂ (fun x : Fin a → Fin a → T → ℂ => fun i j => (g.val * Matrix.of x * h.val) i j) := by
    refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => differentiable_pi.2 fun t => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply]
    fun_prop
  refine hΦ.comp hd.differentiableOn fun x hx => ?_
  have hx' : IsUnit (Matrix.of x) := hx
  exact (g.isUnit.mul hx').mul h.isUnit

theorem UpperTheory.V.Lit.Bor.cxGrp :
    UpperTheory.V.Lit.Bor.CxGrp := by
  intro E _ _ _ a Ξ
  choose Φ hΦ hv using fun k l => UpperTheory.V.Lit.Bor.holExt E a _ (Ξ.reg k l)
  have hv' : ∀ k l (y : GL (Fin a) (Cinf E)),
      Φ k l (fun i j => (GeneralLinearGroup.map (emb E) y).val i j) = Ξ.mat y k l := fun k l y => hv k l y
  have h1 : ∀ k l (y : GL (Fin a) (Cinf E)) (g : GL (Fin a) ((E →+* ℂ) → ℂ)),
      Φ k l (fun i j => (GeneralLinearGroup.map (emb E) y * g).val i j) =
        ∑ m, Ξ.mat y k m * Φ m l (fun i j => g.val i j) := by
    intro k l y g
    have key := UpperTheory.V.Lit.Bor.holId E a (fun x =>
      Φ k l (fun i j => ((GeneralLinearGroup.map (emb E) y).val * Matrix.of x *
        (1 : GL (Fin a) ((E →+* ℂ) → ℂ)).val) i j) - ∑ m, Ξ.mat y k m * Φ m l x)
      ((cxGrp_comp (hΦ k l) _ _).sub
        (DifferentiableOn.fun_sum fun m _ => (hΦ m l).const_mul _)) (fun z => by
          have e := hv' k l (y * z)
          rw [map_mul, map_mul, Matrix.mul_apply] at e
          simp only [hv]
          rw [← e, sub_eq_zero, Units.val_one, mul_one]
          rfl) g
    rw [sub_eq_zero, Units.val_one, mul_one] at key
    exact key
  have h2 : ∀ k l (g h : GL (Fin a) ((E →+* ℂ) → ℂ)),
      Φ k l (fun i j => (g * h).val i j) =
        ∑ m, Φ k m (fun i j => g.val i j) * Φ m l (fun i j => h.val i j) := by
    intro k l g h
    have key := UpperTheory.V.Lit.Bor.holId E a (fun x =>
      Φ k l (fun i j => ((1 : GL (Fin a) ((E →+* ℂ) → ℂ)).val * Matrix.of x * h.val) i j) -
        ∑ m, Φ k m x * Φ m l (fun i j => h.val i j))
      ((cxGrp_comp (hΦ k l) _ _).sub
        (DifferentiableOn.fun_sum fun m _ => (hΦ k m).mul_const _)) (fun z => by
          have e := h1 k l z h
          simp only [hv]
          rw [← e, sub_eq_zero, Units.val_one, one_mul]
          rfl) g
    rw [sub_eq_zero, Units.val_one, one_mul] at key
    exact key
  refine ⟨{ toFun := fun g => Matrix.of fun k l => Φ k l (fun i j => g.val i j)
            map_one' := ?_
            map_mul' := fun g h => ?_ }, Φ, hΦ, fun _ _ _ => rfl, fun y => ?_⟩
  · ext k l
    have e := hv' k l 1
    rw [map_one, map_one] at e
    exact e
  · ext k l
    rw [Matrix.mul_apply]
    exact h2 k l g h
  · ext k l
    exact hv' k l y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LevelCo
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : W →ₗ[ℂ] W) (i : Fin d)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor _ m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

private theorem ex_cmp {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} {m : W ⊗[ℂ] (Fin d → ℂ)} (h : m ≠ 0) :
    ∃ i, cmp i m ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [← sum_cmp m]
  simp [hc]

private theorem rT_map {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T A : Module.End ℂ W)
    (B : Module.End ℂ (Fin d → ℂ)) (h : Commute T A) (m : W ⊗[ℂ] (Fin d → ℂ)) :
    T.rTensor _ (TensorProduct.map A B m) = TensorProduct.map A B (T.rTensor _ m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul]
    congr 1
    exact LinearMap.congr_fun h.eq φ

theorem UpperTheory.V.Lit.Bor.levelCo :
    UpperTheory.V.Lit.Bor.LevelCo := by
  intro E _ _ _ a U hU π Ξ hC hF
  obtain ⟨q, ω, h0, hK, hB⟩ := basicEx E a _ (tensorK π Ξ) (tensorLie π Ξ) hC
  obtain ⟨X, hX⟩ : ∃ X, ω X ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (AlternatingMap.ext hc)
  obtain ⟨i, hi⟩ := ex_cmp hX
  obtain ⟨T, hT, hTK, hTU⟩ := levelOp E a U hU π hF _ hi
  refine ⟨q, ((T.rTensor (Fin Ξ.d → ℂ)).restrictScalars ℝ).compAlternatingMap ω, fun h => hT ?_, fun k Y => ?_,
    fun Y j hj => ?_, fun Y j u hu => ?_⟩
  · have h1 : T.rTensor (Fin Ξ.d → ℂ) (ω X) = 0 := DFunLike.congr_fun h X
    rw [← cmp_rT, h1, map_zero]
  · change T.rTensor (Fin Ξ.d → ℂ) (ω _) = tensorK π Ξ k (T.rTensor (Fin Ξ.d → ℂ) (ω Y))
    rw [hK k Y]
    exact rT_map T _ _ (hTK k) _
  · change T.rTensor (Fin Ξ.d → ℂ) (ω Y) = 0
    rw [hB Y j hj, map_zero]
  · change π.op (.fin u) (cmp j (T.rTensor (Fin Ξ.d → ℂ) (ω Y))) = cmp j (T.rTensor (Fin Ξ.d → ℂ) (ω Y))
    rw [cmp_rT]
    exact hTU _ u hu
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OpenFix
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem open_fix {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

theorem UpperTheory.V.Lit.Bor.sqMem :
    UpperTheory.V.Lit.Bor.SqMem := by
  intro E _ _ _ a ha μ _ r χ hχ φ hφ
  change IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} ∧ _
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    have hl : IsOpen {k | finRep E a k φ = φ} := h.level
    have ho : IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} := by
      refine open_fix (finRep E a) _ (hl.inter (isOpen_ker_chiDet (a := a) χ)) ⟨by simp, by simp⟩ ?_
      rintro k ⟨h1, h2⟩
      have h1' : rt E a (finGL E a k) φ = φ := h1
      have h2' : chiDet a χ (finGL E a k) = 1 := h2
      change rt E a (finGL E a k) (mulChi a χ φ) = _
      rw [rt_mulChi, h1', h2']
      simp
    have hs := sqUniq E a ha r χ hχ φ h.one (by simpa using h.sq [])
    refine ⟨ho, (CuspidalL2GL.memL2_iff_isSqInt (ContAut.continuous_of_isOpen_stab E a _ ho) (fun γ g => ?_) hs.1).2 hs⟩
    rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, h.left]
  | zero =>
    rw [map_zero]
    refine ⟨?_, fun _ _ _ => rfl, MeasureTheory.MemLp.zero⟩
    convert isOpen_univ using 1
    ext k
    simp only [Set.mem_setOf_eq, map_zero, Set.mem_univ]
  | add φ ψ _ _ h h' =>
    rw [map_add (f := _)]
    refine ⟨open_fix (finRep E a) _ (h.1.inter h'.1) ⟨by simp, by simp⟩ ?_,
      fun γ hγ g => congrArg₂ (· + ·) (h.2.1 γ hγ g) (h'.2.1 γ hγ g), h.2.2.add h'.2.2⟩
    rintro k ⟨h1, h2⟩
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) h1 h2)
  | smul c φ _ h =>
    rw [map_smul]
    refine ⟨open_fix (finRep E a) _ h.1 (by simp) ?_,
      fun γ hγ g => congrArg (c • ·) (h.2.1 γ hγ g), h.2.2.const_smul c⟩
    intro k h1
    exact (map_smul _ _ _).trans (congrArg (c • ·) h1)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ZalgCommute
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

namespace UpperTheory.V.Lit.Bor.CasimirCentre

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem zalg_commute {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (o : Op E a) : Commute z (act o) := by
  refine Algebra.adjoin_induction (p := fun x _ => Commute x (act o)) ?_ (fun r => Algebra.commutes r _)
    (fun _ _ _ _ hx hy => hx.add_left hy) (fun _ _ _ _ hx hy => hx.mul_left hy) hz
  rintro _ ⟨τ, u, rfl⟩
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
  | lie X => exact commute_cap_lie τ u X

private theorem uC_shift (r : ℝ) (X : Lie E a) : Cm.uC E a (shift (Cm.ιC E a) r X) = shift (lie E a) r X := by
  rw [shift_apply, shift_apply, map_add (f := _), Cm.uC_ιC, ← algebraMap_smul ℂ (r * ell E a X) (1 : Cm.UC E a), map_smul,
    map_one, algebraMap_smul]

private theorem center_of {z : Cm.UC E a} (h : ∀ X, Commute z (Cm.ιC E a X)) : z ∈ Subalgebra.center ℂ (Cm.UC E a) := by
  have hle : Algebra.adjoin ℂ {x : Cm.UC E a | ∃ τ i j, x = Cm.genC τ i j} ≤ Subalgebra.centralizer ℂ {z} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (((h _).sub_right ((h _).smul_right _)).smul_right _).eq
  rw [Cm.adjoin_genC] at hle
  exact Subalgebra.mem_center_iff.2 fun x => (hle Algebra.mem_top z rfl).symm

end UpperTheory.V.Lit.Bor.CasimirCentre

open UpperTheory.V.Lit.Bor.CasimirCentre in
theorem UpperTheory.V.Lit.Bor.casPi :
    UpperTheory.V.Lit.Bor.CasPi := by
  intro E _ _ _ a n e he π r
  have hL : IsLieHom (shift (Cm.ιC E a) r) := (ellFacts E a).2.2.2 _ _ r Cm.isLieHom_ιC
  have hc : cas (shift (Cm.ιC E a) r) e ∈ Subalgebra.center ℂ (Cm.UC E a) := center_of fun X => by
    have h := casComm E a n e he _ _ hL X
    have h' : Cm.ιC E a X = shift (Cm.ιC E a) r X - (r * ell E a X) • 1 := by rw [shift_apply, add_sub_cancel_right]
    rw [h']
    exact h.sub_right ((Commute.one_right _).smul_right _)
  have hz : cas (shift (lie E a) r) e ∈ Zalg E a := by
    rw [Cm.Zalg_eq_map]
    exact ⟨_, hc, by simp only [cas, map_sum, map_sub, map_mul, uC_shift, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]⟩
  exact π.exists_scalar hz (zalg_commute hz)
end

