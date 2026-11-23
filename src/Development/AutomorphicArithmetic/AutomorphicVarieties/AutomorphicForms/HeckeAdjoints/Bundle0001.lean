module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
public import Mathlib
public import GroundTheory.AutomorphicForms.TensorProductTheorem.CentralCusp
public import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspCentral

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.ConjCusp
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

noncomputable section

namespace UpperTheory.V.Af.Gk

private theorem map_qdet_conj {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (f : A →+* A)
    (hf : ∀ c : ℂ, f (algebraMap ℂ A c) = algebraMap ℂ A (starRingEnd ℂ c)) (X : Fin n → Fin n → A)
    (hX : ∀ i j, f (X i j) = X i j) (u : ℂ) :
    f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet X (starRingEnd ℂ u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, id_eq, Formalism.REAL.Tm, map_add, hX]
  split_ifs <;> simp [hf, map_sub]

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

private def conjOp : Module.End ℂ (Sm E a) →+* Module.End ℂ (Sm E a) where
  toFun z := (conjFn E a).toLinearMap ∘ₛₗ (z ∘ₛₗ (conjFn E a).toLinearMap)
  map_one' := LinearMap.ext fun φ => conjFn_conjFn φ
  map_mul' x y := LinearMap.ext fun φ => by
    change conjFn E a (x (y (conjFn E a φ))) = conjFn E a (x (conjFn E a (conjFn E a (y (conjFn E a φ)))))
    rw [conjFn_conjFn]
  map_zero' := LinearMap.ext fun φ => map_zero (conjFn E a)
  map_add' x y := LinearMap.ext fun φ => map_add (conjFn E a) _ _

private theorem conjOp_apply (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjOp z φ = conjFn E a (z (conjFn E a φ)) := rfl

private theorem conjOp_algebraMap (c : ℂ) :
    conjOp (algebraMap ℂ (Module.End ℂ (Sm E a)) c) = algebraMap ℂ _ (starRingEnd ℂ c) :=
  LinearMap.ext fun φ => by
    rw [conjOp_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smulₛₗ, conjFn_conjFn]

private theorem conjOp_Eop (v : InfinitePlace E) (i j : Fin a) : conjOp (Eop v i j) = Eop v i j :=
  LinearMap.ext fun φ => (congrArg (conjFn E a) (act_conjFn (.lie _) φ)).trans (conjFn_conjFn _)

private theorem conjOp_cap (v : InfinitePlace E) (u : ℂ) :
    conjOp (cap (a := a) v u) = cap v (starRingEnd ℂ u) := by
  refine (map_qdet_conj (conjOp (E := E) (a := a)) conjOp_algebraMap (Eop v) (conjOp_Eop v) _).trans ?_
  refine congrArg (Formalism.REAL.qdet (Eop (a := a) v)) ?_
  simp only [map_add (f := _), map_div₀, map_sub, map_natCast, map_one, map_ofNat]

private theorem conjOp_mem {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) : conjOp z ∈ Zalg E a := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    rw [conjOp_cap]
    exact Algebra.subset_adjoin ⟨τ, _, rfl⟩
  | algebraMap c => rw [conjOp_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private theorem fin_of_conj {s t : Set (Sm E a)} (h : FiniteDimensional ℂ (Submodule.span ℂ s))
    (hst : ∀ y ∈ t, ∃ x ∈ s, conjFn E a x = y) : FiniteDimensional ℂ (Submodule.span ℂ t) := by
  have h1 : (Submodule.span ℂ s).FG := Module.Finite.iff_fg.1 h
  have h2 : FiniteDimensional ℂ ((Submodule.span ℂ s).map (conjFn E a).toLinearMap) :=
    Module.Finite.iff_fg.2 (h1.map _)
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ s).map (conjFn E a).toLinearMap)
    (Submodule.span_le.2 fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := hst y hy
  exact ⟨x, Submodule.subset_span hx, rfl⟩

private theorem isAutForm_conjFn {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (conjFn E a φ) := by
  exact {
    left γ g := by rw [conjFn_apply, conjFn_apply, h.left]
    level := by
      convert h.level using 1
      ext k
      exact (Iff.of_eq (congrArg (· = conjFn E a φ) (act_conjFn (.fin k) φ))).trans (conjFn E a).injective.eq_iff
    kfin := fin_of_conj h.kfin (by
      rintro _ ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, (act_conjFn (.cpt k) φ).symm⟩)
    zfin := fin_of_conj h.zfin (by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨_, ⟨conjOp z, conjOp_mem hz, rfl⟩, ?_⟩
      beta_reduce
      rw [conjOp_apply, conjFn_conjFn])
    growth g := by
      obtain ⟨C, N, h1⟩ := h.growth g
      refine ⟨C, N, fun y => ?_⟩
      rw [conjFn_apply, Complex.norm_conj]
      exact h1 y }

end UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.conjCusp :
    UpperTheory.V.Af.Gk.ConjCusp := by
  intro F _ _ _ a φ h
  refine ⟨isAutForm_conjFn h.1, ?_⟩
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  have key := h.2 r h0 h1 μ 𝓕 hμ hF g
  simp only [conjFn_apply]
  rw [integral_conj, key, map_zero]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HeckeAdj
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.heckeAdj :
    UpperTheory.V.Af.Gk.HeckeAdj := by
  intro F _ _ a w V _ _ ρ H hH x hx ϖ hϖ j
  have hK : ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), GlobalTheory.CuspRep.invT a _ k ∈ GlobalTheory.LFun.KGL w (n := a) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨GlobalTheory.CuspRep.invT a _ k, InvT.map_invT _ k⟩
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have hf := fun (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion F)) V) => GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm F w a) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x
  have e1 := (H.flip x).toAddMonoidHom.map_finsum (hf ρ)
  have e2 := (H x).toAddMonoidHom.map_finsum (hf (ρ.comp (GlobalTheory.CuspRep.invT a (w.adicCompletion F))))
  refine e1.trans ((finsum_congr fun c => ?_).trans e2.symm)
  generalize c.out = g
  change H (_ • ρ g x) x = H x (_ • ρ (GlobalTheory.CuspRep.invT a _ g) x)
  unfold Formalism.UG.Tj
  by_cases hg : g ∈ {g : GL (Fin a) (w.adicCompletion F) | ∃ k ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w),
      ∃ b ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w), g.val = k.val * Formalism.UG.diagJ a ϖ j * b.val}
  · rw [Set.indicator_of_mem hg, Pi.one_apply, one_smul, one_smul]
    obtain ⟨k, hk, b, hb, e⟩ := hg
    obtain ⟨d, rfl⟩ : ∃ d, g = k * d * b := ⟨k⁻¹ * g * b⁻¹, by group⟩
    have hd : d.val = Formalism.UG.diagJ a ϖ j := by
      rw [Units.val_mul, Units.val_mul] at e
      exact (Units.mul_right_inj k).1 ((Units.mul_left_inj b).1 e)
    have hd' : GlobalTheory.CuspRep.invT a _ d = d⁻¹ := by
      rw [← inv_eq_iff_eq_inv]
      apply Units.ext
      rw [InvT.invT_inv_val, hd, Formalism.UG.diagJ, Matrix.diagonal_transpose]
    simp only [map_mul, Module.End.mul_apply, hd']
    rw [hfix b hb, hfix _ (hK b hb)]
    have h1 : H (ρ k (ρ d x)) x = H (ρ d x) x := by
      rw [← hH k (ρ d x) x, hfix k hk]
    have h2 : H x (ρ (GlobalTheory.CuspRep.invT a _ k) (ρ d⁻¹ x)) = H x (ρ d⁻¹ x) := by
      rw [← hH (GlobalTheory.CuspRep.invT a _ k) x (ρ d⁻¹ x), hfix _ (hK k hk)]
    rw [h1, h2, ← hH d x (ρ d⁻¹ x), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · rw [Set.indicator_of_notMem hg]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.IsHermOfInner
section
noncomputable section

open NumberField MeasureTheory UpperTheory.V.TR GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.UnitaryAdmissible

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.Af.Gk

def ToFound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : Sm F a), TR.IsCuspForm φ → φ.1 ∈ cuspForms F a

def LieMatch : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ),
    ∃ e : TR.Lie F a →ₗ[ℝ] (isExpLieAlgebra F a).lieSubalgebra, centralZ F a = centralExp F a • e (oneL F a) ∧
      ∀ X (φ : Sm F a) (h : φ.1 ∈ cuspForms F a), (lieActionCusp F a (e X) ⟨φ.1, h⟩).1 = (TR.lie F a X φ).1

private theorem isHerm_of_inner {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} {π : CuspSub F a} {L : Type}
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] (p : π.V →ₗ[ℂ] L) (h1 : ∀ φ, inner ℂ (p φ) (p φ) = 0 → φ = 0)
    (h2 : ∀ k φ ψ, inner ℂ (p (π.op (.fin k) φ)) (p (π.op (.fin k) ψ)) = inner ℂ (p φ) (p ψ))
    (h3 : ∀ k φ ψ, inner ℂ (p (π.op (.cpt k) φ)) (p (π.op (.cpt k) ψ)) = inner ℂ (p φ) (p ψ))
    (h4 : ∀ X φ ψ, inner ℂ (p (π.op (.lie X) φ)) (p ψ) + inner ℂ (p φ) (p (π.op (.lie X) ψ)) = 0) : ∃ H, IsHerm π H :=
  ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ ψ => inner ℂ (p φ) (p ψ))
    (fun _ _ _ => by rw [map_add (f := _), inner_add_left]) (fun _ _ _ => by rw [map_smul, inner_smul_left]; rfl)
    (fun _ _ _ => by rw [map_add (f := _), inner_add_right]) (fun _ _ _ => by rw [map_smul, inner_smul_right]; rfl), h1, h2, h3, h4⟩

theorem hermEx_of (h1 : ToFound) (h2 : LieMatch) : HermEx := by
  intro F _ _ _ a _ π h0
  obtain ⟨e, hz, he⟩ := h2 F a
  let μ : Measure (Reduction.normOneGL (K := F) (n := a)) := Measure.haar
  let j : π.V →ₗ[ℂ] cuspForms F a :=
    ((Sm F a).subtype ∘ₗ π.V.subtype).codRestrict _ fun φ => h1 F a φ.1 (π.cusp _ φ.2)
  have hl : ∀ X φ, (gkModuleCusp F a).ρ (e X) (j φ) = j (π.op (.lie X) φ) := fun X φ => Subtype.ext (he X φ.1 _)
  have hc : ∀ φ, j φ ∈ centralCuspForms F a := fun φ => mem_centralCuspForms.mpr fun s x => by
    have h3 : lieActionCusp F a (e (oneL F a)) (j φ) = 0 :=
      Subtype.ext ((he _ φ.1 _).trans (congrArg Subtype.val (h0 _ φ.2)))
    have h4 : lieActionCusp F a (centralZ F a) (j φ) = (0 : ℂ) • j φ := by
      rw [hz, map_smul, LinearMap.smul_apply, h3, smul_zero, zero_smul]
    rw [Reduction.centralSection_mul_comm, apply_mul_centralSection h4]
    simp
  let p := CuspidalSpectrum.cuspToL2 μ ∘ₗ j
  have hr : ∀ (g : GlobalTheory.CuspRep.GA F a) (φ φ' ψ ψ' : π.V), φ'.1 = rt F a g φ.1 → ψ'.1 = rt F a g ψ.1 →
      inner ℂ (p φ') (p ψ') = inner ℂ (p φ) (p ψ) := fun g φ φ' ψ ψ' e1 e2 =>
    (congrArg₂ (inner ℂ) (cuspFormLp_rightTranslate_eq_rep μ (hc φ) g (ψ := j φ') (congrArg Subtype.val e1))
      (cuspFormLp_rightTranslate_eq_rep μ (hc ψ) g (ψ := j ψ') (congrArg Subtype.val e2))).trans
      (UnitaryRep.inner_map_map (CuspidalSpectrum.cuspRep μ) _ _ _)
  refine isHerm_of_inner p (fun φ h => ?_) (fun k φ ψ => hr _ _ _ _ _ rfl rfl) (fun k φ ψ => hr _ _ _ _ _ rfl rfl)
    fun X φ ψ => ?_
  · have h5 : (j φ).1 = (0 : cuspForms F a).1 := congrArg Subtype.val (eq_zero_of_petersson_inner_self_eq_zero μ (hc φ) h)
    exact Subtype.ext (Subtype.ext h5)
  · have e1 : p (π.op (.lie X) φ) = CuspidalSpectrum.cuspToL2 μ ((gkModuleCusp F a).ρ (e X) (j φ)) :=
      congrArg (CuspidalSpectrum.cuspToL2 μ) (hl X φ).symm
    have e2 : p (π.op (.lie X) ψ) = CuspidalSpectrum.cuspToL2 μ ((gkModuleCusp F a).ρ (e X) (j ψ)) :=
      congrArg (CuspidalSpectrum.cuspToL2 μ) (hl X ψ).symm
    exact (congrArg₂ (· + ·) (congrArg (inner ℂ · (p ψ)) e1) (congrArg (inner ℂ (p φ)) e2)).trans
      (petersson_inner_lieAlgebra_skewAdjoint μ (e X) (hc φ) (hc ψ))

end UpperTheory.V.Af.Gk
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.PairOfTwist
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

private theorem UpperTheory.V.Af.Gk.opMul_mul_invT {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}
    (χ : HChar E) (o : Op E a) : ((opMul χ o : ℂˣ) : ℂ) * ((opMul χ (invTOp o) : ℂˣ) : ℂ) = 1 := by
  have key : ∀ g : GlobalTheory.CuspRep.GA E a, ((GlobalTheory.CuspRep.chiDet a χ g : ℂˣ) : ℂ) *
      ((GlobalTheory.CuspRep.chiDet a χ (GlobalTheory.CuspRep.invT a _ g) : ℂˣ) : ℂ) = 1 := fun g => by
    rw [InvT.chiDet_invT]
    exact Units.mul_inv _
  cases o with
  | fin k =>
    have := key (GlobalTheory.CuspRep.finGL E a k)
    rw [← InvT.finGL_invT] at this
    exact this
  | cpt k =>
    have := key (infGL E a (Unitary.toUnits k))
    rw [← infGL_invT, invT_toUnits] at this
    exact this
  | lie X => simp [opMul, invTOp]

theorem UpperTheory.V.Af.Gk.pairOfTwist :
    UpperTheory.V.Af.Gk.PairOfTwist := by
  intro F _ _ _ a π χ ⟨B, h1, h2, hf, hc, hl⟩
  let T := π.toTwist χ
  refine ⟨B.compl₁₂ T.toLinearMap T.toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ h
    apply T.injective
    rw [T.map_zero]
    apply h1
    intro ψ
    simpa using h (T.symm ψ)
  · intro ψ h
    apply T.injective
    rw [T.map_zero]
    apply h2
    intro φ
    simpa using h (T.symm φ)
  · intro k φ ψ
    have h := hf k (T φ) (T ψ)
    have e := opMul_mul_invT χ (.fin k : Op F a)
    simp only [T, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← mul_assoc, mul_comm (_ : ℂ) ((opMul χ (.fin k) : ℂˣ) : ℂ)] at h
    erw [e] at h
    rw [one_mul] at h
    exact h
  · intro k φ ψ
    have h := hc k (T φ) (T ψ)
    have e := opMul_mul_invT χ (.cpt k : Op F a)
    simp only [T, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← mul_assoc] at h
    erw [e] at h
    rw [one_mul] at h
    exact h
  · intro X φ ψ
    have h := hl X (T φ) (T ψ)
    have e : (Matrix.of (toL (-(Matrix.of X)ᵀ))).trace = -(Matrix.of X).trace := by
      change (-(Matrix.of X)ᵀ).trace = _
      rw [Matrix.trace_neg, Matrix.trace_transpose]
    simp only [T, CuspSub.op_toTwist, opAdd, opMul, Units.val_one, one_smul, map_add (f := _), map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, e, map_neg] at h
    change B (T _) (T ψ) + B (T φ) (T _) = 0
    linear_combination h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.PairZero
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.pairZero :
    UpperTheory.V.Af.Gk.PairZero := by
  intro F _ _ _ π
  have hs : ∀ g h : GlobalTheory.CuspRep.GA F 0, g = h := fun g h => Units.ext (Subsingleton.elim _ _)
  let e : π.V →ₗ[ℂ] ℂ := (LinearMap.proj 1) ∘ₗ (Sm F 0).subtype ∘ₗ π.V.subtype
  have he : ∀ φ, e φ = φ.1.1 1 := fun _ => rfl
  have hinj : ∀ φ, e φ = 0 → φ = 0 := fun φ h =>
    Subtype.ext <| Subtype.ext <| funext fun g => by rw [hs g 1]; exact h
  have hfin : ∀ k φ, e (π.op (.fin k) φ) = e φ := fun k φ => congrArg φ.1.1 (hs _ _)
  have hcpt : ∀ k φ, e (π.op (.cpt k) φ) = e φ := fun k φ => congrArg φ.1.1 (hs _ _)
  have hlie : ∀ X φ, e (π.op (.lie X) φ) = 0 := fun X φ => by
    rw [Subsingleton.elim X 0]
    exact map_zero (fderiv ℝ (chart φ.1.1 1) (oneL F 0))
  refine ⟨(LinearMap.mul ℂ ℂ).compl₁₂ e e, fun φ h => hinj φ (mul_self_eq_zero.1 (h φ)),
    fun φ h => hinj φ (mul_self_eq_zero.1 (h φ)), fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · change e _ * e _ = e φ * e ψ
    rw [hfin, hfin]
  · change e _ * e _ = e φ * e ψ
    rw [hcpt, hcpt]
  · change e _ * e _ + e _ * e _ = 0
    rw [hlie, hlie, zero_mul, mul_zero, add_zero]
end

