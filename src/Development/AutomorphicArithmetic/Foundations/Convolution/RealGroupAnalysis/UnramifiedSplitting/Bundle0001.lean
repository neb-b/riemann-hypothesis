module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Imports
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.avg :
    ∀ (H M : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [AddCommGroup M] [Module ℂ M]
      (ρ : H →* Module.End ℂ M) (x : M), (∀ᶠ h in 𝓝 (1 : H), ρ h x = x) →
      ∃ s : Finset H, s.Nonempty ∧ ∀ h, ρ h (∑ k ∈ s, ρ k x) = ∑ k ∈ s, ρ k x := by
  intro H M _ _ _ _ _ _ ρ x hx
  have hmul : ∀ a b : H, ρ (a * b) x = ρ a (ρ b x) := fun a b => by
    rw [map_mul, Module.End.mul_apply]
  let S : Subgroup H :=
    { carrier := {h | ρ h x = x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [hmul, hb', ha']
      one_mem' := by
        show ρ 1 x = x
        simp
      inv_mem' := fun {a} ha => by
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        conv_lhs => rw [← ha']
        rw [← hmul]
        simp }
  have hSo : IsOpen (S : Set H) := Subgroup.isOpen_of_mem_nhds S hx
  haveI : Finite (H ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  haveI : Fintype (H ⧸ S) := Fintype.ofFinite _
  have key : ∀ k k' : H, (k : H ⧸ S) = k' → ρ k x = ρ k' x := by
    intro k k' h
    have h2 : ρ (k⁻¹ * k') x = x := QuotientGroup.eq.mp h
    calc ρ k x = ρ k (ρ (k⁻¹ * k') x) := by rw [h2]
      _ = ρ k' x := by rw [← hmul]; simp
  refine ⟨Finset.univ.image (fun q : H ⧸ S => (Quotient.out q : H)),
    ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ((1 : H) : H ⧸ S))⟩, ?_⟩
  intro h
  have hinj : Function.Injective (fun q : H ⧸ S => (Quotient.out q : H)) :=
    fun a b hab => Quotient.out_injective hab
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_image hinj.injOn, map_sum]
  refine Fintype.sum_equiv (ι := H ⧸ S) (κ := H ⧸ S) (MulAction.toPerm h) _ _ ?_
  intro q
  show ρ h (ρ (Quotient.out q) x) = ρ (Quotient.out (h • q)) x
  rw [← hmul]
  apply key
  rw [QuotientGroup.out_eq']
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.RightInv
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private lemma countable_gam (K : Type) [Field K] [NumberField K] : Countable (Gam K) := by
  haveI : Countable K := by
    have : Module.Finite ℚ K := inferInstance
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℚ K
    exact hf.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Function.Injective.countable (f := fun g => (g.1 : Matrix (Fin 2) (Fin 2) K)) Subtype.val_injective
  unfold Gam
  exact (Set.countable_range (ratS K)).to_subtype

theorem UpperTheory.ConvolutionTheory.R2.H.rightInv :
    ∀ (K : Type) [Field K] [NumberField K] (M : Meas K) (u : G1 K → ℂ), (∀ γ g, u (ratS K γ * g) = u g) → IntegrableOn u M.D M.μ →
      ∀ k, IntegrableOn (fun g => u (g * k)) M.D M.μ ∧ ∫ g in M.D, u (g * k) ∂M.μ = ∫ g in M.D, u g ∂M.μ := by
  intro K _ _ M u hu hint k
  haveI := M.haar
  haveI := M.right
  haveI := countable_gam K
  have hmp : MeasurePreserving (· * k) M.μ M.μ := measurePreserving_mul_right M.μ k
  have hemb : MeasurableEmbedding (· * k : G1 K → G1 K) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd : IsFundamentalDomain (Gam K) ((Equiv.mulRight k) '' M.D) M.μ := by
    refine M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  have hinv : ∀ (g : Gam K) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : (· * k : G1 K → G1 K) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D := by
    ext x; simp
  constructor
  · have h1 : IntegrableOn u ((Equiv.mulRight k) '' M.D) M.μ :=
      (M.fund.integrableOn_iff hfd hinv).1 hint
    have h2 := (hmp.integrableOn_comp_preimage hemb).2 h1
    rwa [hpre] at h2
  · have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)
    rw [hpre] at h3
    rw [h3]
    exact hfd.setIntegral_eq M.fund hinv
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.H

variable {K : Type} [Field K] [NumberField K]

private theorem sg_fst (v : P K) (x : Kv v) : (sg v x).1 = 0 := rfl

private theorem sg_snd_self (v : P K) (x : Kv v) : (sg v x).2 v = x := by
  change GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd v x v = x
  rw [GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd_apply, Pi.single_eq_same]

private theorem sg_snd_ne (v : P K) (x : Kv v) {w : P K} (h : w ≠ v) : (sg v x).2 w = 0 := by
  change GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd v x w = 0
  rw [GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd_apply, Pi.single_eq_of_ne h]

private theorem ext_a {a b : A K} (h1 : a.1 = b.1) (h2 : ∀ w : P K, a.2 w = b.2 w) : a = b :=
  Prod.ext h1 (FiniteAdeleRing.ext K h2)

private theorem sg_add (v : P K) (x y : Kv v) : sg v (x + y) = sg v x + sg v y := by
  refine ext_a (by change 0 = (sg v x).1 + (sg v y).1; simp [sg_fst]) fun w => ?_
  by_cases h : w = v
  · subst h
    change _ = (sg w x).2 w + (sg w y).2 w
    simp only [sg_snd_self]
  · change _ = (sg v x).2 w + (sg v y).2 w
    simp only [sg_snd_ne _ _ h, add_zero]

private theorem sg_mul (v : P K) (a : A K) (x : Kv v) : a * sg v x = sg v (cp v a * x) := by
  refine ext_a (by change a.1 * (sg v x).1 = _; simp [sg_fst]) fun w => ?_
  change a.2 w * (sg v x).2 w = _
  by_cases h : w = v
  · subst h
    simp only [sg_snd_self]; rfl
  · simp only [sg_snd_ne _ _ h, mul_zero]

private theorem cp_sg (v : P K) (x : Kv v) : cp v (sg v x) = x := sg_snd_self v x

private theorem idl_eq (v : P K) (x : (Kv v)ˣ) :
    ((idl v x : (A K)ˣ) : A K) = 1 + sg v ((x : Kv v) - 1) := by
  refine ext_a ?_ fun w => ?_
  · change (1 : InfiniteAdeleRing K) = 1 + (sg v _).1
    rw [sg_fst, add_zero]
  · change (idl v x : (A K)ˣ).val.2 w = 1 + (sg v _).2 w
    by_cases h : w = v
    · subst h
      rw [sg_snd_self]
      have : (localIdele K w x).val.2 w = x := by
        classical
        exact Pi.mulSingle_eq_same w _
      change (localIdele K w x).val.2 w = _
      rw [this]; ring
    · rw [sg_snd_ne _ _ h, add_zero]
      have : (localIdele K v x).val.2 w = 1 := by
        classical
        exact Pi.mulSingle_eq_of_ne h _
      exact this

private theorem cont_sg (v : P K) : Continuous (sg v) :=
  continuous_const.prodMk (GroundTheory.Global.continuous_finiteAdeleSingleAdd (K := K) v)

private theorem lc_fst (v : P K) (g : GL (Fin 2) (Kv v)) (i j : Fin 2) :
    ((lc v g).val i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
  have h : Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (Af K)) (lc v g) = 1 := by
    change Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (Af K))
      (finGL K 2 (locGL K 2 v g)) = 1
    rw [← Fb.finEmb_eq]
    exact congrArg Prod.fst
      (GroundTheory.Automorphic.AutomorphicForm.prodEquiv_finEmb (locGL K 2 v g))
  exact congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing K) => x.val i j) h

private theorem lc_snd (v w : P K) (g : GL (Fin 2) (Kv v)) (i j : Fin 2) :
    ((lc v g).val i j).2 w =
      (Matrix.GeneralLinearGroup.map (pLoc K w) (locGL K 2 v g)).val i j := by
  have h := pFin_finGL (E := K) (a := 2) (locGL K 2 v g)
  have e : ((lc v g).val i j).2 = (locGL K 2 v g).val i j :=
    congrArg (fun x : GL (Fin 2) (Af K) => x.val i j) h
  rw [e]
  rfl

private theorem one_fst (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem one_snd (w : P K) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).2 w = (1 : Matrix (Fin 2) (Fin 2) (Kv w)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem lc_entry (v : P K) (g : GL (Fin 2) (Kv v)) (i j : Fin 2) :
    (lc v g).val i j = (1 : Matrix (Fin 2) (Fin 2) (A K)) i j +
      sg v (g.val i j - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i j) := by
  refine ext_a ?_ fun w => ?_
  · change _ = ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).1 + (sg v _).1
    rw [lc_fst, sg_fst, add_zero, one_fst]
  · rw [lc_snd]
    change _ = ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).2 w + (sg v _).2 w
    by_cases h : w = v
    · subst h
      rw [pLoc_locGL, sg_snd_self, one_snd]
      ring
    · rw [pLoc_locGL_of_ne h, sg_snd_ne _ _ h, add_zero, one_snd]
      rfl

private theorem ab_idl (v : P K) (x : (Kv v)ˣ) : ab (idl v x) = ‖(x : Kv v)‖ := by
  have e : idl v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x := by
    apply Units.ext
    rfl
  rw [e]
  exact GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x

private theorem norm_of_val (v : P K) (x : Kv v) (n : ℤ) (h : Valued.v x = WithZero.exp n) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [NumberField.FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  rfl

private theorem ab_unif (v : P K) (ϖ : (Kv v)ˣ) (h : IsU ϖ) :
    ab (idl v ϖ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [ab_idl, norm_of_val v _ (-1) h, _root_.zpow_neg_one]

private theorem ab_unit (v : P K) (x : (Kv v)ˣ) (h : Valued.v (x : Kv v) = 1) : ab (idl v x) = 1 := by
  rw [ab_idl, norm_of_val v _ 0 (by simpa using h), zpow_zero]

private theorem cont_val_lc (v : P K) :
    Continuous fun g : GL (Fin 2) (Kv v) => ((lc v g : GL (Fin 2) (A K)) : Matrix (Fin 2) (Fin 2) (A K)) := by
  refine continuous_matrix fun i j => ?_
  simp only [lc_entry]
  refine continuous_const.add ((cont_sg v).comp (Continuous.sub ?_ continuous_const))
  exact Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Kv v))) i j

private theorem cont_lc (v : P K) : Continuous (lc v) := by
  refine Units.continuous_iff.2 ⟨cont_val_lc v, ?_⟩
  have e : (fun g : GL (Fin 2) (Kv v) => (((lc v g)⁻¹ : GL (Fin 2) (A K)) : Matrix (Fin 2) (Fin 2) (A K))) =
      (fun g : GL (Fin 2) (Kv v) => ((lc v g : GL (Fin 2) (A K)) : Matrix (Fin 2) (Fin 2) (A K))) ∘
        fun g => g⁻¹ := by
    funext g
    simp only [Function.comp, map_inv]
  exact e ▸ (cont_val_lc v).comp continuous_inv

end UpperTheory.ConvolutionTheory.R2.H

theorem UpperTheory.ConvolutionTheory.R2.H.sgLaws :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K), (∀ x y, sg v (x + y) = sg v x + sg v y) ∧ (∀ (a : A K) x, a * sg v x = sg v (cp v a * x)) ∧ (∀ x, cp v (sg v x) = x) ∧
      (∀ x, ((idl v x : (A K)ˣ) : A K) = 1 + sg v ((x : Kv v) - 1)) ∧
      (∀ (g : GL (Fin 2) (Kv v)) i j, (lc v g).val i j = (1 : Matrix (Fin 2) (Fin 2) (A K)) i j + sg v (g.val i j - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i j)) ∧
      (∀ ϖ, IsU ϖ → ab (idl v ϖ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) ∧ (∀ x : (Kv v)ˣ, Valued.v (x : Kv v) = 1 → ab (idl v x) = 1) ∧
      (∀ x, (sg v x).1 = 0 ∧ ∀ v' ≠ v, (sg v x).2 v' = 0) ∧ Continuous (lc v) ∧ Continuous (sg v) := by
  intro K _ _ v
  exact ⟨sg_add v, sg_mul v, cp_sg v, idl_eq v, lc_entry v, ab_unif v, ab_unit v,
    fun x => ⟨sg_fst v x, fun _ h => sg_snd_ne v x h⟩, cont_lc v, cont_sg v⟩
end

