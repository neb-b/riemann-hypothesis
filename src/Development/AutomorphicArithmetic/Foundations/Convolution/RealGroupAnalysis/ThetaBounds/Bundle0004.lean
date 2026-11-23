module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OpsFock
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private lemma infiniteProjection_placeEmbed (w : InfinitePlace F) (t : ℝ) : TR.pInf F (Fo.at1 w t) = Pi.single w t := by
  change (TR.infEq F).symm (TR.infEq F (Pi.single w t)) = _
  exact RingEquiv.symm_apply_apply _ _

private lemma placeEmbedReal_zero (w : InfinitePlace F) : Fo.at1 w 0 = 0 := by
  simp [Fo.at1]

private lemma placeEmbedReal_finitePart (w : InfinitePlace F) (t : ℝ) : (Fo.at1 w t).2 = 0 := rfl

private lemma shift_zero (w : InfinitePlace F) (i : Fin 4) (v : V4 F) :
    v + Pi.single i (Fo.at1 w 0) = v := by
  simp [placeEmbedReal_zero]

private lemma finPart_shift (w : InfinitePlace F) (i : Fin 4) (v : V4 F) (t : ℝ) :
    finPartPi (v + Pi.single i (Fo.at1 w t)) = finPartPi v := by
  funext j
  by_cases h : j = i
  · subst h
    simp only [finPartPi, Pi.add_apply, Pi.single_eq_same]
    change (v j).2 + (Fo.at1 w t).2 = (v j).2
    rw [placeEmbedReal_finitePart, add_zero]
  · simp [finPartPi, Pi.single_eq_of_ne h]

private lemma coord_shift (w w' : InfinitePlace F) (i j : Fin 4) (v : V4 F) (t : ℝ) :
    ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ) =
      ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ) := by
  by_cases h : j = i
  · subst h
    by_cases h' : w' = w
    · subst h'
      simp [map_add (f := _), infiniteProjection_placeEmbed]
    · simp [map_add (f := _), infiniteProjection_placeEmbed, h', Pi.single_eq_of_ne h']
  · simp [h, Pi.single_eq_of_ne h]

private lemma lin_der (a c : ℂ) : HasDerivAt (fun t : ℝ => a + c * (t : ℂ)) c 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).const_add a
  simpa using h

private lemma coord_mem (j : Fin 4) (w : InfinitePlace F) :
    (fun v : V4 F => ((TR.pInf F (v j) w : ℝ) : ℂ)) ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F) :=
  Algebra.subset_adjoin ⟨j, w, rfl⟩

private lemma poly_der (w : InfinitePlace F) (i : Fin 4) {p : V4 F → ℂ}
    (hp : p ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F)) :
    ∃ p' ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∀ v,
      HasDerivAt (fun t : ℝ => p (v + Pi.single i (Fo.at1 w t))) (p' v) 0 := by
  unfold UpperTheory.ConvolutionTheory.R2.polyFn at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, w', rfl⟩ := hx
    refine ⟨algebraMap ℂ _ (if j = i ∧ w' = w then 1 else 0), Subalgebra.algebraMap_mem _ _, fun v => ?_⟩
    have e : (fun t : ℝ => ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ)) =
        fun t : ℝ => ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ) :=
      funext fun t => coord_shift w w' i j v t
    rw [e]
    exact lin_der _ _
  | algebraMap r =>
    exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    exact ⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩
  | mul x y hxa hya hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    refine ⟨x' * y + x * y', add_mem (mul_mem hxm hya) (mul_mem hxa hym), fun v => ?_⟩
    have h := (hx v).mul (hy v)
    simp only [shift_zero] at h
    exact h

private noncomputable def Qf (δ : F) (v : V4 F) : ℂ :=
  ((∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w : ℝ) : ℂ)

private lemma Qf_mem (δ : F) : Qf δ ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F) := by
  have e : Qf δ = ∑ w, ((fun v : V4 F => ((TR.pInf F (v 0) w : ℝ) : ℂ)) ^ 2 +
      (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ^ 2 +
      algebraMap ℂ (V4 F → ℂ) 2 * ((fun v : V4 F => ((TR.pInf F (v 2) w : ℝ) : ℂ)) ^ 2 -
        algebraMap ℂ (V4 F → ℂ) ((TR.pInf F (rt δ) w : ℝ) : ℂ) *
          (fun v : V4 F => ((TR.pInf F (v 3) w : ℝ) : ℂ)) ^ 2)) := by
    funext v
    have h2 : ∀ x, TR.pInf F (2 : A F) x = 2 := fun x => by
      rw [map_ofNat]; rfl
    simp [Qf, Finset.sum_apply, map_add (f := _), map_mul, map_sub, map_pow, h2]
  rw [e]
  refine sum_mem fun w _ => ?_
  exact add_mem (add_mem (pow_mem (coord_mem 0 w) 2) (pow_mem (coord_mem 1 w) 2))
    (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (pow_mem (coord_mem 2 w) 2)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (coord_mem 3 w) 2))))

private lemma gauss_der (δ : F) (w : InfinitePlace F) (i : Fin 4) :
    ∃ q ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∀ v, HasDerivAt
      (fun t : ℝ => UpperTheory.ConvolutionTheory.R2.gauss δ (v + Pi.single i (Fo.at1 w t)))
      (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v) 0 := by
  obtain ⟨q, hq, hd⟩ := poly_der w i (Qf_mem δ)
  refine ⟨algebraMap ℂ _ (-(Real.pi : ℂ)) * q, mul_mem (Subalgebra.algebraMap_mem _ _) hq, fun v => ?_⟩
  have h := ((hd v).const_mul (-(Real.pi : ℂ))).cexp
  simp only [shift_zero] at h
  exact h

private def Gen (δ : F) : Set (V4 F → ℂ) :=
  {φ : V4 F → ℂ | ∃ p ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
    φ = fun v => p v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v)}

private lemma cw_coord_mul_mem_span_gen_of_mem (δ : F) (w : InfinitePlace F) (i : Fin 4) {f : V4 F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Gen δ)) :
    (fun v => Fo.cw w (v i) * f v) ∈ Submodule.span ℂ (Gen δ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨(fun v : V4 F => ((TR.pInf F (v i) w : ℝ) : ℂ)) * p,
      mul_mem (coord_mem i w) hp, g, hg, ?_⟩
    funext v
    simp [Fo.cw, mul_assoc]
  | zero =>
    have : (fun v : V4 F => Fo.cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
      funext v; simp
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun v : V4 F => Fo.cw w (v i) * (x + y) v) =
        (fun v => Fo.cw w (v i) * x v) + fun v => Fo.cw w (v i) * y v := by
      funext v; simp [mul_add]
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    have : (fun v : V4 F => Fo.cw w (v i) * (c • x) v) = c • fun v => Fo.cw w (v i) * x v := by
      funext v; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ _ hx

private lemma span_d (δ : F) (w : InfinitePlace F) (i : Fin 4) {f : V4 F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Gen δ)) :
    ∃ f' ∈ Submodule.span ℂ (Gen δ), ∀ v,
      HasDerivAt (fun t : ℝ => f (v + Pi.single i (Fo.at1 w t))) (f' v) 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    obtain ⟨p', hp', hdp⟩ := poly_der w i hp
    obtain ⟨q, hq, hdq⟩ := gauss_der δ w i
    refine ⟨fun v => (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v),
      Submodule.subset_span ⟨p' + p * q, add_mem hp' (mul_mem hp hq), g, hg, rfl⟩, fun v => ?_⟩
    have h := ((hdp v).mul (hdq v)).mul_const (g (finPartPi v))
    simp only [shift_zero] at h
    simp only [finPart_shift]
    have e : (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v) =
        (p' v * UpperTheory.ConvolutionTheory.R2.gauss δ v + p v * (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v)) * g (finPartPi v) := by
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    rw [e]
    exact h
  | zero => exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    exact ⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩
  | smul c x _ hx =>
    obtain ⟨x', hxm, hx⟩ := hx
    exact ⟨c • x', Submodule.smul_mem _ _ hxm, fun v => (hx v).const_mul c⟩

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.opsFock :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), OpsFock D O := by
  intro F E _ _ _ _ _ _ _ D O w i φ hφ
  have hs : φ.1 ∈ Submodule.span ℂ (Gen D.δ) := hφ
  refine ⟨?_, ?_⟩
  · have e : (O.x w i φ).1 = fun v => Fo.cw w (v i) * φ.1 v := funext fun v => O.x_apply w i φ v
    change (O.x w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)
    rw [e]
    exact cw_coord_mul_mem_span_gen_of_mem D.δ w i hs
  · obtain ⟨f', hf', hd⟩ := span_d D.δ w i hs
    have e : (O.d w i φ).1 = f' := funext fun v => (O.d_spec w i φ v).unique (hd v)
    change (O.d w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)
    rw [e]
    exact hf'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RtInv
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.rtInv :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], RtInv F := by
  intro F _ _ _ M u hu k
  haveI := M.haar
  haveI := M.right
  have hmp : MeasurePreserving (· * k) M.μ M.μ := measurePreserving_mul_right M.μ k
  have hemb : MeasurableEmbedding (· * k : G1 F → G1 F) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd : IsFundamentalDomain (Gam F) ((Equiv.mulRight k) '' M.D) M.μ := by
    refine M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  have hinv : ∀ (g : Gam F) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : (· * k : G1 F → G1 F) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D := by
    ext x; simp
  have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq M.fund hinv
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.SumCoordPl
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private theorem fiber_eq (w : InfinitePlace E) :
    (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have h' : InfinitePlace.mk w.embedding = InfinitePlace.mk τ := by rw [InfinitePlace.mk_embedding, h]
    exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
  · rintro (rfl | rfl)
    · exact InfinitePlace.mk_embedding w
    · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

private theorem emb_ne (w : InfinitePlace E) : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
  InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
    (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))

private theorem pl_eq (τ : E →+* ℂ) : Fo.pl F τ = (InfinitePlace.mk τ).comap (algebraMap F E) := by
  rw [InfinitePlace.comap_mk]; rfl

private theorem sum_coord_pl {M : Type*} [AddCommGroup M] [Module ℂ M] (s : Cinf E) (G : InfinitePlace F → M) :
    ∑ τ : E →+* ℂ, coord τ s • G (Fo.pl F τ) = ∑ v, ((trI F s v : ℝ) : ℂ) • G v := by
  have hr : ∀ v, ((trI F s v : ℝ) : ℂ) • G v =
      ∑ w : InfinitePlace E, (if w.comap (algebraMap F E) = v then ((2 * (s w).re : ℝ) : ℂ) • G v else 0) := by
    intro v
    simp only [trI]
    rw [Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  simp only [hr]
  rw [Finset.sum_comm, ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), fiber_eq, Finset.sum_pair (emb_ne w), pl_eq, pl_eq,
    InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding,
    UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding, ← add_smul, Complex.add_conj]

private theorem theta_ne (D : Dat F E) : D.θ ≠ 0 := by
  rw [← D.b1]; exact D.b.ne_zero 1

private theorem dE_sum (D : Dat F E) (O : Fo.Ops F) (τ : E →+* ℂ) :
    O.dE D τ 0 0 + O.dE D τ 1 1 = -O.h (Fo.pl F τ) := by
  have ht : τ D.θ ≠ 0 := fun h => theta_ne D ((map_eq_zero τ).1 h)
  have h2 : (2 : Module.End ℂ (S4 F)) = 1 + 1 := one_add_one_eq_two.symm
  simp only [Fo.Ops.dE, Fo.Ops.X, Fo.Ops.DX, Fo.Ops.h, Fin.sum_univ_two, Fin.sum_univ_four, h2]
  simp only [Fin.isValue, if_true, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val]
  generalize τ D.θ = t at ht
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  match_scalars <;> field_simp <;> ring

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.dLCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), DLCen D O := by
  intro F E _ _ _ _ _ _ _ D O
  refine ⟨fun s => ?_, fun Y Y' => ?_, fun c Y => ?_, fun s => ?_⟩
  · have hz : ∀ i j, zE s i j = if i = j then s else 0 := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [zE, GlobalTheory.CuspRep.toL, Matrix.scalar_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.sum_univ_two, hz]
    simp only [Fin.isValue, if_true, one_ne_zero, zero_ne_one, if_false, map_zero, zero_smul, add_zero, zero_add]
    rw [← smul_add, dE_sum, smul_neg]
  · simp only [Fo.Ops.dL, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (Y + Y') i j = Y i j + Y' i j from rfl, map_add (f := _)]
  · simp only [Fo.Ops.dL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (c • Y) i j = c • Y i j from rfl, UpperTheory.V.FieldIso.coord_smul, Complex.real_smul, mul_smul]
  · rw [sum_coord_pl s (fun v => TR.Eop v 0 0 + TR.Eop v 1 1)]
    have hz : zF (trI F s) = ∑ v, trI F s v • (TR.toL (Matrix.single 0 0 (Pi.single v 1)) + TR.toL (Matrix.single 1 1 (Pi.single v 1)) : TR.Lie F 2) := by
      ext i j w
      fin_cases i <;> fin_cases j <;> simp [zF, TR.toL, Matrix.scalar_apply, Finset.sum_apply, Pi.single_apply, Matrix.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, map_add (f := _)]
    first
      | rfl
      | exact (Complex.coe_smul _ _).symm
      | (ext φ g; rfl)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_mono' {F : Type} [Field F] [NumberField F]
    {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : K ⊆ K') (N : ℕ) (v : V4 F) :
    wt K N v ≤ wt K' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

private theorem majorant {F : Type} [Field F] [NumberField F] {G : V4 F → ℂ}
    (hG : G ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    ∃ K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ N, ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ‖G v‖ ≤ B * wt K N v := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    have hgc : Continuous g := ((mem_finiteSchwartzBruhatPi F).mp hg).1.continuous
    have hgs : HasCompactSupport g := ((mem_finiteSchwartzBruhatPi F).mp hg).2
    obtain ⟨C₂, h₂⟩ := hgc.bounded_above_of_compact_support hgs
    refine ⟨tsupport g, hgs.isCompact, fun N => ?_⟩
    obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_le_inv_one_add_pow φ N
    refine ⟨C₁ * max C₂ 0, mul_nonneg hC₁ (le_max_right _ _), fun v => ?_⟩
    simp only [schwartzBruhatTensorPi, norm_mul]
    by_cases hx : finPartPi v ∈ tsupport g
    · rw [wt, if_pos hx]
      calc ‖φ (infPartPi v)‖ * ‖g (finPartPi v)‖
          ≤ (C₁ * ((1 + ‖infPartPi v‖) ^ N)⁻¹) * max C₂ 0 :=
            mul_le_mul (h₁ _) ((h₂ _).trans (le_max_left _ _)) (norm_nonneg _)
              (mul_nonneg hC₁ (inv_nonneg.2 (by positivity)))
        _ = C₁ * max C₂ 0 * ((1 + ‖infPartPi v‖) ^ N)⁻¹ := by ring
    · rw [wt, if_neg hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  | zero =>
    exact ⟨∅, isCompact_empty, fun N => ⟨0, le_rfl, fun v => by simp⟩⟩
  | add G H _ _ hG hH =>
    obtain ⟨K₁, hK₁, h₁⟩ := hG
    obtain ⟨K₂, hK₂, h₂⟩ := hH
    refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun N => ?_⟩
    obtain ⟨B₁, hB₁, b₁⟩ := h₁ N
    obtain ⟨B₂, hB₂, b₂⟩ := h₂ N
    refine ⟨B₁ + B₂, add_nonneg hB₁ hB₂, fun v => ?_⟩
    calc ‖(G + H) v‖ ≤ ‖G v‖ + ‖H v‖ := norm_add_le _ _
      _ ≤ B₁ * wt K₁ N v + B₂ * wt K₂ N v := add_le_add (b₁ v) (b₂ v)
      _ ≤ B₁ * wt (K₁ ∪ K₂) N v + B₂ * wt (K₁ ∪ K₂) N v :=
          add_le_add (mul_le_mul_of_nonneg_left (wt_mono' Set.subset_union_left N v) hB₁)
            (mul_le_mul_of_nonneg_left (wt_mono' Set.subset_union_right N v) hB₂)
      _ = (B₁ + B₂) * wt (K₁ ∪ K₂) N v := by ring
  | smul c G _ hG =>
    obtain ⟨K, hK, h⟩ := hG
    refine ⟨K, hK, fun N => ?_⟩
    obtain ⟨B, hB, b⟩ := h N
    refine ⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (b v) (norm_nonneg c)

theorem UpperTheory.ConvolutionTheory.R2.Ff.wtBound :
    ∀ (F : Type) [Field F] [NumberField F], WtBound F := by
  intro F _ _ φ
  refine ⟨continuous_of_mem_schwartzBruhatPi φ.2, ?_⟩
  obtain ⟨K, hK, h⟩ := majorant φ.2
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨B, _, b⟩ := h N
  exact ⟨B, fun _ _ v => b v⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtEqComp
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

set_option synthInstance.maxSize 1000

private theorem wt_eq_comp {F : Type} [Field F] [NumberField F]
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) :
    wt (F := F) K N =
      (fun p : (Fin 4 → mixedEmbedding.mixedSpace F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) =>
        ((1 + ‖p.1‖) ^ N)⁻¹ * K.indicator (fun _ => (1 : ℝ)) p.2) ∘ splitEquivPi F (Fin 4) := by
  funext v
  by_cases h : finPartPi v ∈ K
  · simp [wt, splitEquivPi_apply, h]
  · simp [wt, splitEquivPi_apply, h]

theorem UpperTheory.ConvolutionTheory.R2.Ff.wtInt :
    ∀ (F : Type) [Field F] [NumberField F], WtInt F := by
  intro F _ _
  refine ⟨Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1, fun K hK => ?_⟩
  rw [wt_eq_comp, measurePreserving_splitEquivPi.integrable_comp_emb
    (splitEquivPi F (Fin 4)).measurableEmbedding]
  refine Integrable.mul_prod (f := fun x : Fin 4 → mixedEmbedding.mixedSpace F => ((1 + ‖x‖) ^ (Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1))⁻¹)
    (g := fun y => K.indicator (fun _ => (1 : ℝ)) y) ?_ ?_
  · have h := integrable_one_add_norm (E := Fin 4 → mixedEmbedding.mixedSpace F)
      (μ := mixedMeasurePi F) (r := ((Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1 : ℕ) : ℝ))
      (by push_cast; linarith)
    refine h.congr (Eventually.of_forall fun x => ?_)
    have hx : (0 : ℝ) ≤ 1 + ‖x‖ := by positivity
    simp only [Real.rpow_neg hx, Real.rpow_natCast]
  · exact (integrable_indicator_iff hK.measurableSet).2
      (integrableOn_const hK.measure_lt_top.ne)
end

