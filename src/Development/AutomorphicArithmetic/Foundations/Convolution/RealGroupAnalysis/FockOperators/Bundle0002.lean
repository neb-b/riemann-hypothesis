module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import GroundTheory.GlobalFields.TateThesis.Bundle0008
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.GaussMem
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical SchwartzMap

private theorem mixed_coord {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : V4 F) (i : Fin 4)
    (w : InfinitePlace F) :
    (infPartPi v i).1 ⟨w, IsTotallyReal.isReal w⟩ = TR.pInf F (v i) w := by
  rfl

private theorem pInf_rt_neg {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ φ : F →+* ℝ, φ δ < 0) (w : InfinitePlace F) : TR.pInf F (rt δ) w < 0 := by
  have h : TR.pInf F (rt δ) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ :=
    by
      change InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (algebraMap F w.Completion δ) = _
      rw [AbsoluteValue.Completion.algebraMap_def]
      exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) (WithAbs.toAbs _ δ)
  rw [h]
  exact hδ _

private noncomputable def coordLin {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) :
    (Fin 4 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4 × InfinitePlace F) where
  toFun u := WithLp.toLp 2 fun p => c p * (u p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩
  map_add' u u' := by
    ext p
    simp [mul_add]
  map_smul' a u := by
    ext p
    simp [mul_left_comm]

private theorem coordLin_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) (u : Fin 4 → mixedEmbedding.mixedSpace F) (p : Fin 4 × InfinitePlace F) :
    coordLin c u p = c p * (u p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩ := by
  rfl

private theorem coordLin_inj {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) (hc : ∀ p, c p ≠ 0) : LinearMap.ker (coordLin c) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro u hu
  funext i
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have h := congrArg (fun y : EuclideanSpace ℝ (Fin 4 × InfinitePlace F) => y (i, w.1)) hu
    simp only [coordLin_apply] at h
    exact (mul_eq_zero.1 h).resolve_left (hc _)
  · exact (InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1) w.2).elim

private theorem exists_sch {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ φ : F →+* ℝ, φ δ < 0) :
    ∃ f : 𝓢(Fin 4 → mixedEmbedding.mixedSpace F, ℂ), ∀ v : V4 F, f (infPartPi v) = gauss δ v := by
  let k : Fin 4 × InfinitePlace F → ℝ := fun p => ![1, 1, 2, -2 * TR.pInf F (rt δ) p.2] p.1
  have hk : ∀ p, 0 < k p := by
    rintro ⟨i, w⟩
    have hd := pInf_rt_neg δ hδ w
    fin_cases i <;> simp [k] <;> linarith
  let c : Fin 4 × InfinitePlace F → ℝ := fun p => Real.sqrt (k p)
  have hc : ∀ p, c p ≠ 0 := fun p => (Real.sqrt_pos.2 (hk p)).ne'
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith (coordLin c) (coordLin_inj c hc)
  let T := LinearMap.toContinuousLinearMap (coordLin c)
  have hT : ∀ u, T u = coordLin c u := fun _ => rfl
  have hg : Function.HasTemperateGrowth T := T.hasTemperateGrowth
  have hK' : AntilipschitzWith K T := hK
  refine ⟨SchwartzMap.compCLMOfAntilipschitz ℂ hg hK' (gaussianSchwartz _), fun v => ?_⟩
  have hn : ‖T (infPartPi v)‖ ^ 2 = ∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hs : ∀ i, (T (infPartPi v) (i, w)) ^ 2 = k (i, w) * TR.pInf F (v i) w ^ 2 := fun i => by
      rw [hT, coordLin_apply, mixed_coord, mul_pow, Real.sq_sqrt (hk _).le]
    simp only [hs, Fin.sum_univ_four, k, map_add (f := _), map_mul, map_sub, map_pow, map_ofNat, Pi.add_apply,
      Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.ofNat_apply]
    simp
    ring
  rw [SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply, gaussianSchwartz_apply, hn, gauss]
  push_cast
  rfl

theorem UpperTheory.ConvolutionTheory.R2.Fo.gaussMem :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), (fun v => gauss D.δ v * g (finPartPi v)) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  intro F E _ _ _ _ _ _ _ D g hg
  obtain ⟨f, hf⟩ := exists_sch D.δ D.neg
  have h : (fun v => gauss D.δ v * g (finPartPi v)) = schwartzBruhatTensorPi f g := by
    funext v
    simp only [schwartzBruhatTensorPi, hf]
  rw [h]
  exact schwartzBruhatTensorPi_mem f hg
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.HermAct
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)

private noncomputable def st (X : Matrix (Fin 2) (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E) := (X.map D.bar)ᵀ

private theorem st_mul (X Y : Matrix (Fin 2) (Fin 2) (A E)) : st D (X * Y) = st D Y * st D X := by
  simp only [st, Matrix.map_mul, Matrix.transpose_mul]

private theorem st_st (X : Matrix (Fin 2) (Fin 2) (A E)) : st D (st D X) = X := by
  ext i j
  simp [st]

private theorem st_herm (v : V4 F) : st D (D.herm v) = D.herm v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [st, Dat.herm, Dat.bar_mkE]

private theorem mkE_of_fixed {z : A E} (h : D.bar z = z) : D.mkE (D.co z 0) 0 = z := by
  rw [D.mkE_base]
  exact (D.eq_am_of_bar_eq h).symm

private theorem herm_unherm {X : Matrix (Fin 2) (Fin 2) (A E)} (h : st D X = X) :
    D.herm (D.unherm X) = X := by
  have e : ∀ i j, D.bar (X j i) = X i j := fun i j => congrFun (congrFun h i) j
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Dat.herm, Dat.unherm] using mkE_of_fixed D (e 0 0)
  · simpa [Dat.herm, Dat.unherm] using D.mkE_co (X 0 1)
  · have := D.bar_mkE (D.co (X 0 1) 0) (D.co (X 0 1) 1)
    rw [D.mkE_co, e] at this
    simpa [Dat.herm, Dat.unherm] using this.symm
  · simpa [Dat.herm, Dat.unherm] using mkE_of_fixed D (e 1 1)

private noncomputable def eps (K : Type) [Field K] [NumberField K] : A K := (0, 1)

private theorem eps_mul_snd (a : A F) : (eps F * a).2 = a.2 := one_mul _

private theorem am_eps : am E (eps F) = eps E := by
  refine Prod.ext ?_ ?_
  · exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))
  · exact map_one (AdeleBaseChange.finiteAdeleMap F E)

end UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed

open UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed in
theorem UpperTheory.ConvolutionTheory.R2.Fo.hermAct :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E), (∀ h v, D.herm (D.act h v) = h.val * D.herm v * (h.val.map D.bar)ᵀ) ∧ (∀ u t, D.bar (D.mkE u t) = D.mkE u (-t)) ∧
    (∀ z, D.mkE (D.co z 0) (D.co z 1) = z) ∧ ∀ u t : A F, (D.mkE u t).2 = 0 → u.2 = 0 ∧ t.2 = 0 := by
  intro F E _ _ _ _ _ _ _ D
  refine ⟨fun h v => ?_, D.bar_mkE, D.mkE_co, fun u t h0 => ?_⟩
  · change D.herm (D.unherm (h.val * D.herm v * st D h.val)) = h.val * D.herm v * st D h.val
    apply herm_unherm
    rw [st_mul, st_mul, st_st, st_herm, mul_assoc]
  · have h1 : D.mkE (eps F * u) (eps F * t) = D.mkE 0 0 := by
      rw [← D.am_mul_mkE, am_eps, D.mkE_zero]
      refine Prod.ext (zero_mul _) ?_
      rw [eps_mul_snd, h0]
      rfl
    obtain ⟨hu, ht⟩ := D.mkE_inj h1
    exact ⟨(eps_mul_snd u).symm.trans (congrArg Prod.snd hu), (eps_mul_snd t).symm.trans (congrArg Prod.snd ht)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.MixApply
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private noncomputable def UpperTheory.ConvolutionTheory.R2.Fo.mix {F : Type} [Field F] [NumberField F] (g h : G1 F) : G1 F :=
  ⟨Matrix.of fun i j => ((g i j).1, (h i j).2), by
    have hg := g.det_coe
    have hh := h.det_coe
    rw [Matrix.det_fin_two] at hg hh ⊢
    have h1 := congrArg Prod.fst hg
    have h2 := congrArg Prod.snd hh
    exact Prod.ext h1 h2⟩

private theorem UpperTheory.ConvolutionTheory.R2.Fo.mix_apply {F : Type} [Field F] [NumberField F] (g h : G1 F) (i j : Fin 2) :
    mix g h i j = ((g i j).1, (h i j).2) := rfl

private theorem UpperTheory.ConvolutionTheory.R2.Fo.mix_one {F : Type} [Field F] [NumberField F] : mix (1 : G1 F) 1 = 1 := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  exact Prod.ext rfl rfl

private theorem UpperTheory.ConvolutionTheory.R2.Fo.mix_mul {F : Type} [Field F] [NumberField F] (g h g' h' : G1 F) :
    mix (g * g') (h * h') = mix g h * mix g' h' := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  change mix (g * g') (h * h') i j = (mix g h * mix g' h') i j
  rw [mix_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact Prod.ext rfl rfl

theorem UpperTheory.ConvolutionTheory.R2.Fo.proj :
    ∀ (F : Type) [Field F] [NumberField F], ∃ pi pf : G1 F →* G1 F, Continuous pf ∧ ∀ g, FinOne (pi g) ∧ InfOne (pf g) ∧ pi g * pf g = g ∧
    (∀ i j, (pi g i j).1 = (g i j).1) ∧ ∀ i j, (pf g i j).2 = (g i j).2 := by
  intro F _ _
  refine ⟨⟨⟨fun g => mix g 1, mix_one⟩, fun g h => ?_⟩, ⟨⟨fun g => mix 1 g, mix_one⟩, fun g h => ?_⟩, ?_, fun g => ⟨fun _ _ => rfl, fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  · change mix (g * h) 1 = mix g 1 * mix h 1
    rw [← mix_mul, one_mul]
  · change mix 1 (g * h) = mix 1 g * mix 1 h
    rw [← mix_mul, one_mul]
  · change Continuous fun g : G1 F => mix 1 g
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    have h : Continuous fun g : G1 F => g i j :=
      (continuous_apply_apply i j).comp continuous_subtype_val
    exact continuous_const.prodMk (continuous_snd.comp h)
  · change mix g 1 * mix 1 g = g
    rw [← mix_mul, one_mul, mul_one]
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    exact Prod.ext rfl rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PerpCpt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.perpCpt :
    ∀ (F : Type) [Field F] [NumberField F] (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)), ∃ K : Set (FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
    ∀ x : A F, (∀ a : A F, a.1 = 0 → a.2 ∈ Λ → ψ (a * x) = 1) → x.2 ∈ K := by
  intro F _ _ Λ
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset (K := F) (W := (Λ : Set (FiniteAdeleRing (𝓞 F) F)))
    (Λ.isOpen.mem_nhds Λ.zero_mem)
  refine ⟨(idealFiniteAdeles (traceDualIdeal F J) : Set (FiniteAdeleRing (𝓞 F) F)),
    isCompact_idealFiniteAdeles _, fun x hx => ?_⟩
  refine (forall_finiteAdelicChar_mul_eq_one_iff J x.2).1 fun y hy => ?_
  have h := hx (finiteAdeleInr y) rfl (hJ hy)
  have e : finiteAdeleInr y * x = finiteAdeleInr (y * x.2) := by
    refine Prod.ext ?_ rfl
    change (0 : _) * x.1 = 0
    exact zero_mul _
  rw [e] at h
  rw [finiteAdelicChar_apply]
  exact Circle.ext h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.QuaternaryFormPolarization
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private noncomputable def Bf {F : Type} [Field F] [NumberField F] (δ : F)
    (a y : Fin 4 → FiniteAdeleRing (𝓞 F) F) : FiniteAdeleRing (𝓞 F) F :=
  2 * (a 2 * y 2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * (a 3 * y 3)) - a 1 * y 0 - a 0 * y 1

private theorem continuous_Bf {F : Type} [Field F] [NumberField F] (δ : F) :
    Continuous fun p : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) =>
      Bf δ p.1 p.2 := by
  unfold Bf
  fun_prop

private theorem fin_level {F : Type} [Field F] [NumberField F] (δ : F)
    {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    ∃ Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F), ∀ a : Fin 4 → FiniteAdeleRing (𝓞 F) F,
      (∀ i, a i ∈ Λ) → ∀ y, g (y + a) = g y ∧ (finiteAdelicChar F (Bf δ a y) : ℂ) * g y = g y := by
  obtain ⟨hl, hc⟩ := hg
  have hev := IsLocallyConstant.iff_eventually_eq g |>.1 hl
  have hP1 : IsOpen {p : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) |
      g (p.2 + p.1) = g p.2} := by
    rw [isOpen_iff_eventually]
    intro p hp
    have h1 : ∀ᶠ q : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) in 𝓝 p,
        g (q.2 + q.1) = g (p.2 + p.1) :=
      ((continuous_snd.add continuous_fst).tendsto p).eventually (hev _)
    have h2 : ∀ᶠ q : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) in 𝓝 p,
        g q.2 = g p.2 :=
      (continuous_snd.tendsto p).eventually (hev _)
    filter_upwards [h1, h2] with q e1 e2
    change g (q.2 + q.1) = g q.2
    rw [e1, e2]
    exact hp
  have hχ : IsLocallyConstant fun x : FiniteAdeleRing (𝓞 F) F => (finiteAdelicChar F x : ℂ) := by
    have := isLocallyConstant_finiteAdelicChar_mul (K := F) (1 : FiniteAdeleRing (𝓞 F) F)
    simpa using this
  have hP2 : IsOpen {p : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) |
      (finiteAdelicChar F (Bf δ p.1 p.2) : ℂ) = 1} :=
    (hχ.isOpen_fiber 1).preimage (continuous_Bf δ)
  obtain ⟨u, w, hu, -, h0u, hSw, huw⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : Fin 4 → FiniteAdeleRing (𝓞 F) F)))
    (t := tsupport g) hc (hP1.inter hP2) (by
      rintro ⟨a, y⟩ ⟨ha, -⟩
      obtain rfl : a = 0 := ha
      refine ⟨by simp, ?_⟩
      change (finiteAdelicChar F (Bf δ 0 y) : ℂ) = 1
      have : Bf δ 0 y = 0 := by simp [Bf]
      rw [this, AddChar.map_zero_eq_one, Circle.coe_one])
  have hu0 : u ∈ 𝓝 (0 : Fin 4 → FiniteAdeleRing (𝓞 F) F) := hu.mem_nhds (h0u rfl)
  rw [nhds_pi, Filter.mem_pi] at hu0
  obtain ⟨I, -, t, ht, hIt⟩ := hu0
  have hN : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.mpr ht
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset hN
  refine ⟨⟨idealFiniteAdeles J, isOpen_idealFiniteAdeles J⟩, fun a ha y => ?_⟩
  have hmem : ∀ b : Fin 4 → FiniteAdeleRing (𝓞 F) F, (∀ i, b i ∈ idealFiniteAdeles J) → b ∈ u :=
    fun b hb => hIt fun i _ => Set.mem_iInter.1 (hJ (hb i)) i
  have ha' : ∀ i, a i ∈ idealFiniteAdeles J := ha
  have hau : a ∈ u := hmem a ha'
  have hnau : -a ∈ u := hmem (-a) fun i => neg_mem (ha' i)
  by_cases hy : y ∈ tsupport g
  · obtain ⟨e1, e2⟩ := huw (Set.mk_mem_prod hau (hSw hy))
    have e2' : (finiteAdelicChar F (Bf δ a y) : ℂ) = 1 := e2
    refine ⟨e1, ?_⟩
    rw [e2', one_mul]
  · have hy0 : g y = 0 := image_eq_zero_of_notMem_tsupport hy
    refine ⟨?_, by rw [hy0, mul_zero]⟩
    by_cases hy' : y + a ∈ tsupport g
    · have e1 : g (y + a + -a) = g (y + a) := (huw (Set.mk_mem_prod hnau (hSw hy'))).1
      rw [add_neg_cancel_right] at e1
      exact e1.symm
    · rw [hy0]
      exact image_eq_zero_of_notMem_tsupport hy'

private theorem quaternaryForm_polarization {F : Type} [Field F] [NumberField F] (δ : F) (a v : V4 F)
    (ha : ∀ i, (a i).1 = 0) :
    ψ (B4 δ a v) = (finiteAdelicChar F (Bf δ (finPartPi a) (finPartPi v)) : ℂ) := by
  have : B4 δ a v = finiteAdeleInr (Bf δ (finPartPi a) (finPartPi v)) := by
    refine Prod.ext ?_ ?_
    · change (2 : InfiniteAdeleRing F) * ((a 2).1 * (v 2).1 - (rt δ).1 * ((a 3).1 * (v 3).1)) - (a 1).1 * (v 0).1 - (a 0).1 * (v 1).1 = 0
      simp [ha]
    · have h2 : (2 : A F).2 = (2 : FiniteAdeleRing (𝓞 F) F) := map_ofNat (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) 2
      change (2 : FiniteAdeleRing (𝓞 F) F) * ((a 2).2 * (v 2).2 - (rt δ).2 * ((a 3).2 * (v 3).2)) - (a 1).2 * (v 0).2 - (a 0).2 * (v 1).2 = Bf δ (finPartPi a) (finPartPi v)
      rfl
  rw [ψ, this, finiteAdelicChar_apply]

private theorem level_of_mem {F : Type} [Field F] [NumberField F] (δ : F) {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    ∃ Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F), ∀ a : V4 F, (∀ i, (a i).1 = 0 ∧ (a i).2 ∈ Λ) →
      ∀ v, f (v + a) = f v ∧ ψ (B4 δ a v) * f v = f v := by
  induction hf using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨Λ, hΛ⟩ := fin_level δ hg
    refine ⟨Λ, fun a ha v => ?_⟩
    obtain ⟨e1, e2⟩ := hΛ (finPartPi a) (fun i => (ha i).2) (finPartPi v)
    have hinf : infPartPi (v + a) = infPartPi v := by
      funext i
      have : (v + a) i = ((v i).1, (v i).2 + (a i).2) := by
        refine Prod.ext ?_ rfl
        change (v i).1 + (a i).1 = (v i).1
        rw [(ha i).1, add_zero]
      simp only [infPartPi, this]
    have hfin : finPartPi (v + a) = finPartPi v + finPartPi a := rfl
    refine ⟨?_, ?_⟩
    · simp only [schwartzBruhatTensorPi, hinf, hfin, e1]
    · simp only [schwartzBruhatTensorPi]
      rw [quaternaryForm_polarization δ a v fun i => (ha i).1, mul_left_comm, e2]
  | zero =>
    exact ⟨⊤, fun _ _ _ => ⟨rfl, by simp⟩⟩
  | add G H _ _ hG hH =>
    obtain ⟨Λ, hΛ⟩ := hG
    obtain ⟨Λ', hΛ'⟩ := hH
    refine ⟨Λ ⊓ Λ', fun a ha v => ?_⟩
    obtain ⟨e1, e2⟩ := hΛ a (fun i => ⟨(ha i).1, (ha i).2.1⟩) v
    obtain ⟨e1', e2'⟩ := hΛ' a (fun i => ⟨(ha i).1, (ha i).2.2⟩) v
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, e1, e1']
    · simp only [Pi.add_apply, mul_add, e2, e2']
  | smul c G _ hG =>
    obtain ⟨Λ, hΛ⟩ := hG
    refine ⟨Λ, fun a ha v => ?_⟩
    obtain ⟨e1, e2⟩ := hΛ a ha v
    refine ⟨?_, ?_⟩
    · simp only [Pi.smul_apply, e1]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, e2]

theorem UpperTheory.ConvolutionTheory.R2.Fo.fixEx :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), (∀ φ : S4 F, ∃ Λ, φ ∈ Fix δ Λ) ∧ ∀ Λ Λ', Λ ≤ Λ' → Fix δ Λ' ≤ Fix δ Λ := by
  intro F _ _ δ
  refine ⟨fun φ => ?_, fun Λ Λ' h φ hφ a ha v => hφ a (fun i => ⟨(ha i).1, h (ha i).2⟩) v⟩
  obtain ⟨Λ, hΛ⟩ := level_of_mem δ φ.2
  exact ⟨Λ, fun a ha v => hΛ a ha v⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.SetIntegralMulRight
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
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

private lemma setIntegral_mul_right (K : Type) [Field K] [NumberField K] (M : Meas K) (u : G1 K → ℂ)
    (hu : ∀ γ g, u (ratS K γ * g) = u g) (k : G1 K) :
    ∫ g in M.D, u (g * k) ∂M.μ = ∫ g in M.D, u g ∂M.μ := by
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
  have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq M.fund hinv

theorem UpperTheory.ConvolutionTheory.R2.Fo.moveG :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ), (∀ γ g, f (ratGL F 2 γ * g) = f g) → ∀ (φ : S4 F) (g₀ : G1 F),
    lift W M f (W.Om g₀ φ) = lift W M (fun x => f (x * gl g₀⁻¹)) φ := by
  intro F E _ _ _ _ _ _ _ D W M f hf φ g₀
  funext h
  have hu : ∀ γ g, (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) (ratS F γ * g) =
      (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) g := by
    intro γ g
    have h1 : gl (ratS F γ * g) * dM (nu F h) * gl g₀⁻¹ =
        ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * (gl g * dM (nu F h) * gl g₀⁻¹) := by
      rw [gl_mul, gl_ratS]; group
    have h2 : W.Om (ratS F γ * g) (W.L h φ) = W.Om (ratS F γ) (W.Om g (W.L h φ)) := by
      rw [map_mul, Module.End.mul_apply]
    show f (gl (ratS F γ * g) * dM (nu F h) * gl g₀⁻¹) * Th (W.Om (ratS F γ * g) (W.L h φ)).1 = _
    rw [h1, hf, h2, W.th_Om]
  have key := setIntegral_mul_right F M (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) hu (cD (nu F h) g₀)
  refine Eq.trans (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)) key
  have h1 : gl (g * cD (nu F h) g₀) * dM (nu F h) * gl g₀⁻¹ = gl g * dM (nu F h) := by
    have hi : gl g₀⁻¹ = (gl g₀)⁻¹ := map_inv Matrix.SpecialLinearGroup.toGL g₀
    rw [gl_mul, gl_cD, hi]; group
  have h2 : W.L h (W.Om g₀ φ) = W.Om (cD (nu F h) g₀) (W.L h φ) := by
    have := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (W.comm h g₀)
    simpa only [Module.End.mul_apply] using this
  have h3 : W.Om (g * cD (nu F h) g₀) (W.L h φ) = W.Om g (W.L h (W.Om g₀ φ)) := by
    rw [h2, map_mul, Module.End.mul_apply]
  show f (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om g₀ φ))).1 =
    f (gl (g * cD (nu F h) g₀) * dM (nu F h) * gl g₀⁻¹) * Th (W.Om (g * cD (nu F h) g₀) (W.L h φ)).1
  rw [h1, h3]
end

