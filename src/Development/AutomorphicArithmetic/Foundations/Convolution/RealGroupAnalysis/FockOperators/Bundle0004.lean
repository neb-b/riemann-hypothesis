module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.ActFin
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F]
  [_root_.NumberField.IsTotallyComplex E]

private theorem adeleMap_snd (a : A F) (ha : a.2 = 0) : (AdeleBaseChange.adeleMap F E a).2 = 0 := by
  change AdeleBaseChange.finiteAdeleMap F E a.2 = 0
  rw [ha, map_zero]

private theorem mkE_snd (D : Dat F E) (u t : A F) (hu : u.2 = 0) (ht : t.2 = 0) : (D.mkE u t).2 = 0 := by
  change (AdeleBaseChange.adeleMap F E u).2 + (AdeleBaseChange.adeleMap F E t).2 * (rt D.θ : A E).2 = 0
  rw [adeleMap_snd u hu, adeleMap_snd t ht, zero_mul, add_zero]

private theorem mkE_sub (D : Dat F E) (u t u' t' : A F) :
    D.mkE (u - u') (t - t') = D.mkE u t - D.mkE u' t' := by
  simp only [Dat.mkE, map_sub]
  ring

private theorem snd_sub (a b : A E) : (a - b).2 = a.2 - b.2 := rfl

private theorem bar_snd (D : Dat F E) (z z' : A E) (h : z.2 = z'.2) : (D.bar z).2 = (D.bar z').2 := by
  obtain ⟨-, h2, h3, h4⟩ := hermAct F E D
  have hw : (z - z').2 = 0 := by rw [snd_sub, h, sub_self]
  have h5 := h4 (D.co (z - z') 0) (D.co (z - z') 1) (by rw [h3]; exact hw)
  have h6 : D.bar (z - z') = D.mkE (D.co (z - z') 0) (-D.co (z - z') 1) := by rw [← h2, h3]
  have h7 : (D.bar (z - z')).2 = 0 := by
    rw [h6]
    refine mkE_snd D _ _ h5.1 ?_
    change -(D.co (z - z') 1).2 = 0
    rw [h5.2, neg_zero]
  rw [map_sub, snd_sub] at h7
  exact sub_eq_zero.1 h7

private theorem mkE_inj (D : Dat F E) (a b a' b' : A F) (h : (D.mkE a b).2 = (D.mkE a' b').2) :
    a.2 = a'.2 ∧ b.2 = b'.2 := by
  obtain ⟨-, -, -, h4⟩ := hermAct F E D
  have h5 := h4 (a - a') (b - b') (by rw [mkE_sub, snd_sub, h, sub_self])
  exact ⟨sub_eq_zero.1 h5.1, sub_eq_zero.1 h5.2⟩

end

theorem UpperTheory.ConvolutionTheory.R2.Fo.actFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (y : GL (Fin 2) (Cinf E)) v, finPartPi (D.act (infGL E 2 y) v) = finPartPi v := by
  intro F E _ _ _ _ _ _ _ D y v
  have h1 := (hermAct F E D).1 (infGL E 2 y) v
  have hg : ∀ i j, pFin E ((infGL E 2 y).val i j) = (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j := fun i j =>
    congrArg (fun g : GL (Fin 2) (Af E) => g.val i j) (pFin_infGL y)
  have hone : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := by
    intro i j
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]
  have hb : ∀ i j, pFin E (D.bar ((infGL E 2 y).val i j)) = (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j := by
    intro i j
    have e : pFin E (D.bar ((infGL E 2 y).val i j)) = pFin E (D.bar ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j)) :=
      bar_snd D _ _ ((hg i j).trans (hone i j))
    rw [e, hone]
    congr 1
    by_cases e' : i = j
    · subst e'; simp
    · simp [Matrix.one_apply_ne e']
  have hm1 : (infGL E 2 y).val.map (pFin E) = 1 := by
    exact Matrix.ext fun i j => hg i j
  have hm2 : (((infGL E 2 y).val.map D.bar)ᵀ).map (pFin E) = 1 := by
    refine Matrix.ext fun i j => ?_
    have := hb j i
    simp only [Matrix.map_apply, Matrix.transpose_apply]
    rw [this, Matrix.one_apply, Matrix.one_apply]
    simp [eq_comm]
  have hH : (D.herm (D.act (infGL E 2 y) v)).map (pFin E) = (D.herm v).map (pFin E) := by
    rw [h1, Matrix.map_mul, Matrix.map_mul, hm1, hm2, one_mul, mul_one]
  have e00 := congrFun (congrFun hH 0) 0
  have e01 := congrFun (congrFun hH 0) 1
  have e11 := congrFun (congrFun hH 1) 1
  have a1 := mkE_inj D _ _ _ _ (show (D.mkE _ 0).2 = (D.mkE _ 0).2 from e00)
  have a2 := mkE_inj D _ _ _ _ (show (D.mkE _ _).2 = (D.mkE _ _).2 from e01)
  have a3 := mkE_inj D _ _ _ _ (show (D.mkE _ 0).2 = (D.mkE _ 0).2 from e11)
  funext i
  fin_cases i
  · exact a3.1
  · exact a1.1
  · exact a2.1
  · exact a2.2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AtLaws
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.atLaws :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F), (∀ t : ℝ, ψ (at1 w t) = Complex.exp (cc * t)) ∧ (∀ t, (at1 w t).2 = 0) ∧ (∀ t, TR.pInf F (at1 w t) = Pi.single w t) ∧
    (∀ s t, at1 w (s + t) = at1 w s + at1 w t) ∧ at1 w 0 = 0 ∧ (∀ t a, at1 w t * a = at1 w (t * TR.pInf F a w)) ∧
    (∀ a : A F, a.2 = 0 → a = ∑ w', at1 w' (TR.pInf F a w')) ∧ ∀ t i, finPartPi (Pi.single i (at1 w t) : V4 F) = 0 := by
  intro F _ _ _ w
  have hp : ∀ (w' : InfinitePlace F) (t : ℝ), TR.pInf F (at1 w' t) = Pi.single w' t := fun _ t => (TR.infEq F).symm_apply_apply _
  have h2 : ∀ (w' : InfinitePlace F) (t : ℝ), (at1 w' t).2 = 0 := fun _ t => rfl
  have hfin : ∀ x y : A F, (x + y).2 = x.2 + y.2 := fun _ _ => rfl
  have hmul : ∀ x y : A F, (x * y).2 = x.2 * y.2 := fun _ _ => rfl
  refine ⟨fun t => ?_, h2 w, hp w, fun s t => ?_, ?_, fun t a => ?_, fun a ha => ?_, fun t i => ?_⟩
  · rw [(UpperTheory.ConvolutionTheory.R2.C.splitA F).2 (at1 w t), hp, h2, AddChar.map_zero_eq_one, Circle.coe_one, mul_one,
      Finset.prod_eq_single w]
    · simp [cc]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ w) h
  · refine TR.ad_ext ?_ ?_
    · rw [map_add (f := _), hp, hp, hp, Pi.single_add]
    · change (at1 w (s + t)).2 = (at1 w s + at1 w t).2
      rw [hfin, h2, h2, h2, add_zero]
  · refine TR.ad_ext ?_ ?_
    · rw [hp, map_zero, Pi.single_zero]
    · change (at1 w 0).2 = (0 : A F).2
      rw [h2]
      rfl
  · refine TR.ad_ext ?_ ?_
    · rw [map_mul, hp, hp]
      ext w'
      by_cases h : w' = w
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    · change (at1 w t * a).2 = (at1 w (t * TR.pInf F a w)).2
      rw [h2, hmul, h2, zero_mul]
  · refine TR.ad_ext ?_ ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
        simp_rw [hp]
        ext w'
        simp [Finset.sum_apply, Pi.single_apply]
    · change a.2 = (∑ w', at1 w' (TR.pInf F a w')).2
      rw [ha]
      have : ∀ s : Finset (InfinitePlace F), (∑ w' ∈ s, at1 w' (TR.pInf F a w')).2 = 0 := by
        intro s
        induction s using Finset.induction_on with
        | empty => rfl
        | insert b s hb ih => rw [Finset.sum_insert hb, hfin, h2, ih, add_zero]
      exact (this _).symm
  · funext j
    by_cases h : j = i
    · subst h
      simp [finPartPi, h2]
    · simp [finPartPi, Pi.single_eq_of_ne h]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CoeffB
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem coeffB {F : Type} [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) (j : Fin 4) :
    ∃ c : F, c ≠ 0 ∧ ∃ i : Fin 4, ∀ (a₀ : A F) (v : V4 F), B4 δ (Pi.single i a₀) v = a₀ * (rt c * v j) := by
  fin_cases j
  · refine ⟨-1, by simp, 1, fun a₀ v => ?_⟩
    simp [B4, Pi.single_apply]
  · refine ⟨-1, by simp, 0, fun a₀ v => ?_⟩
    simp [B4, Pi.single_apply]
  · refine ⟨2, by simp, 2, fun a₀ v => ?_⟩
    have h2 : rt (2 : F) = (2 : A F) := map_ofNat _ 2
    simp [B4, Pi.single_apply]
    rw [h2]
    ring
  · refine ⟨-2 * δ, by simp [hδ], 3, fun a₀ v => ?_⟩
    have h2 : algebraMap F (A F) 2 = (2 : A F) := map_ofNat _ 2
    simp [B4, Pi.single_apply]
    rw [h2]
    ring

private theorem fixCpt {F : Type} [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0)
    (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)) :
    ∃ K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K' ∧
      ∀ φ ∈ Fix δ Λ, ∀ v : V4 F, φ.1 v ≠ 0 → (fun j => (v j).2) ∈ K' := by
  obtain ⟨K, hK, hKp⟩ := perpCpt F Λ
  choose c hc i hi using coeffB δ hδ
  refine ⟨Set.univ.pi fun j => (fun k => (rt (c j)⁻¹ : A F).2 * k) '' K,
    isCompact_univ_pi fun j => hK.image (continuous_const.mul continuous_id), ?_⟩
  intro φ hφ v hv j _
  refine ⟨(rt (c j) * v j).2, hKp _ fun a ha1 ha2 => ?_, ?_⟩
  · have hmem : ∀ l, ((Pi.single (i j) a : V4 F) l).1 = 0 ∧ ((Pi.single (i j) a : V4 F) l).2 ∈ Λ := by
      intro l
      by_cases hl : l = i j
      · subst hl
        simpa using ⟨ha1, ha2⟩
      · simp [Pi.single_eq_of_ne hl, Λ.zero_mem]
    have h := (hφ _ hmem v).2
    rw [hi j a v] at h
    exact mul_right_cancel₀ hv (by rw [h, one_mul])
  · have h : rt (c j)⁻¹ * (rt (c j) * v j) = v j := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hc j), map_one, one_mul]
    exact congrArg Prod.snd h

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacFd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)), FiniteDimensional ℂ ↥(Vac D.δ ⊓ Fix D.δ Λ) := by
  intro F E _ _ _ _ _ _ _ D Λ
  have hδ : D.δ ≠ 0 := by
    intro h
    have h2 : D.θ ^ 2 = 0 := by rw [D.sq, h, map_zero]
    have h3 : D.θ = 0 := by simpa using h2
    exact D.b.ne_zero 1 (by rw [D.b1, h3])
  obtain ⟨K', hK', hKp⟩ := fixCpt D.δ hδ Λ
  have hU : ∀ y ∈ K', {z : Fin 4 → FiniteAdeleRing (𝓞 F) F | ∀ i, z i - y i ∈ Λ} ∈ 𝓝 y := fun y _ => by
    have ho : IsOpen {z : Fin 4 → FiniteAdeleRing (𝓞 F) F | ∀ i, z i - y i ∈ Λ} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i =>
        Λ.isOpen.preimage ((continuous_apply i).sub continuous_const)
    exact ho.mem_nhds fun i => by simp [Λ.zero_mem]
  obtain ⟨t, -, ht⟩ := hK'.elim_nhds_subcover _ hU
  let T : ↥(Vac D.δ ⊓ Fix D.δ Λ) →ₗ[ℂ] (t → ℂ) :=
    { toFun := fun φ y => φ.1.1 (fun i => ((0, y.1 i) : A F))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective T ((injective_iff_map_eq_zero T).2 fun φ hφ => ?_)
  ext1
  ext1
  funext v
  by_contra hv
  have hv' : φ.1.1 v ≠ 0 := hv
  have hmem := ht (hKp φ.1 φ.2.2 v hv')
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hmem
  obtain ⟨y, hy, hyv⟩ := hmem
  have hfix := (φ.2.2 (fun i => ((0, (v i).2 - y i) : A F)) (fun i => ⟨rfl, hyv i⟩)
    (fun i => ((0, y i) : A F))).1
  have hsum : ((fun i => ((0, y i) : A F)) + fun i => ((0, (v i).2 - y i) : A F)) = fun i => ((0, (v i).2) : A F) := by
    funext i
    ext1
    · simp
    · simp
  have hfix' : φ.1.1 (fun i => ((0, (v i).2) : A F)) = φ.1.1 (fun i => ((0, y i) : A F)) :=
    (congrArg (fun u => φ.1.1 u) hsum).symm.trans hfix
  have hz : φ.1.1 (fun i => ((0, y i) : A F)) = 0 := congrFun hφ ⟨y, hy⟩
  have hvac := φ.2.1 v (fun i => ((0, (v i).2) : A F)) rfl
  rw [hfix', hz, zero_mul] at hvac
  exact hv' ((mul_eq_zero.1 hvac).resolve_right (Complex.exp_ne_zero _))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkLe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkLe :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F), (∀ w i, ∀ φ ∈ Fock δ, O.x w i φ ∈ Fock δ) ∧ ∀ N ≤ Vac δ, ∀ m, O.Fk N m ≤ Fock δ := by
  intro F _ _ _ δ O
  have hF : ∀ φ : S4 F, (φ : V4 F → ℂ) ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F),
        ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ = fun v => p v * gauss δ v * g (finPartPi v)} → φ ∈ Fock δ := fun _ h => h
  have hx : ∀ w i, ∀ φ ∈ Fock δ, O.x w i φ ∈ Fock δ := by
    intro w i φ hφ
    have hc : (fun v : V4 F => cw w (v i)) ∈ polyFn (F := F) :=
      Algebra.subset_adjoin ⟨i, w, rfl⟩
    have key : ∀ f : V4 F → ℂ, f ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F),
        ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ = fun v => p v * gauss δ v * g (finPartPi v)} →
        (fun v => cw w (v i) * f v) ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F),
        ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ = fun v => p v * gauss δ v * g (finPartPi v)} := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨p, hp, g, hg, rfl⟩ := hf
        refine Submodule.subset_span ⟨(fun v : V4 F => cw w (v i)) * p, mul_mem hc hp, g, hg, ?_⟩
        funext v
        simp only [Pi.mul_apply]
        ring
      | zero =>
        have : (fun v : V4 F => cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
          funext v
          simp
        rw [this]
        exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : (fun v : V4 F => cw w (v i) * (a + b) v) =
            (fun v => cw w (v i) * a v) + fun v => cw w (v i) * b v := by
          funext v
          simp only [Pi.add_apply]
          ring
        rw [this]
        exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : (fun v : V4 F => cw w (v i) * (c • a) v) = c • fun v => cw w (v i) * a v := by
          funext v
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [this]
        exact Submodule.smul_mem _ c ha
    have hφ' := key φ.1 hφ
    have e : ((O.x w i φ : S4 F) : V4 F → ℂ) = fun v => cw w (v i) * φ.1 v := by
      funext v
      exact O.x_apply w i φ v
    apply hF
    rw [e]
    exact hφ'
  refine ⟨hx, fun N hN m => ?_⟩
  have hvac : Vac δ ≤ Fock δ := by
    intro φ hφ
    obtain ⟨g, hg, e⟩ := vacForm F δ φ hφ
    apply hF
    refine Submodule.subset_span ⟨1, one_mem _, g, hg, ?_⟩
    rw [e]
    funext v
    simp
  induction m with
  | zero => exact hN.trans hvac
  | succ m ih =>
    refine sup_le ih (iSup_le fun w => iSup_le fun i => ?_)
    rintro _ ⟨φ, hφ, rfl⟩
    exact hx w i φ (ih hφ)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FockEx
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private def PF (δ : F) (O : Ops F) (f : V4 F → ℂ) : Prop :=
  ∃ Λ m, ∃ φ ∈ O.Fk (Vac δ ⊓ Fix δ Λ) m, φ.1 = f

private theorem fk_mono {δ : F} {O : Ops F} {Λ Λ' : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)} {m m' : ℕ}
    (hΛ : Λ' ≤ Λ) (hm : m ≤ m') {φ : S4 F} (hφ : φ ∈ O.Fk (Vac δ ⊓ Fix δ Λ) m) :
    φ ∈ O.Fk (Vac δ ⊓ Fix δ Λ') m' :=
  (fkBasic F O).1 _ _ (inf_le_inf_left _ ((fixEx F δ).2 _ _ hΛ)) m m' hm hφ

private theorem PF.add {δ : F} {O : Ops F} {f f' : V4 F → ℂ} (h : PF δ O f) (h' : PF δ O f') :
    PF δ O (f + f') := by
  obtain ⟨Λ, m, φ, hφ, rfl⟩ := h
  obtain ⟨Λ', m', φ', hφ', rfl⟩ := h'
  exact ⟨Λ ⊓ Λ', max m m', φ + φ',
    add_mem (fk_mono inf_le_left (le_max_left _ _) hφ) (fk_mono inf_le_right (le_max_right _ _) hφ'), rfl⟩

private theorem PF.smul {δ : F} {O : Ops F} {f : V4 F → ℂ} (c : ℂ) (h : PF δ O f) :
    PF δ O (c • f) := by
  obtain ⟨Λ, m, φ, hφ, rfl⟩ := h
  exact ⟨Λ, m, c • φ, Submodule.smul_mem _ c hφ, rfl⟩

private theorem PF.zero (δ : F) (O : Ops F) : PF δ O 0 :=
  ⟨⊤, 0, 0, zero_mem _, rfl⟩

private theorem PF.coord {δ : F} {O : Ops F} {f : V4 F → ℂ} (i : Fin 4) (w : InfinitePlace F) (h : PF δ O f) :
    PF δ O ((fun v => ((TR.pInf F (v i) w : ℝ) : ℂ)) * f) := by
  obtain ⟨Λ, m, φ, hφ, rfl⟩ := h
  exact ⟨Λ, m + 1, O.x w i φ, (fkBasic F O).2.1 _ m w i φ hφ, funext fun v => O.x_apply w i φ v⟩

private theorem PF.poly {δ : F} {O : Ops F} {p : V4 F → ℂ} (hp : p ∈ polyFn (F := F)) :
    ∀ f, PF δ O f → PF δ O (p * f) := by
  refine Algebra.adjoin_induction (p := fun p _ => ∀ f, PF δ O f → PF δ O (p * f)) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨i, w, rfl⟩ f hf
    exact PF.coord i w hf
  · intro c f hf
    have : (algebraMap ℂ (V4 F → ℂ) c) * f = c • f := by
      rw [Algebra.smul_def]
    rw [this]
    exact PF.smul c hf
  · intro a b _ _ ha hb f hf
    rw [add_mul]
    exact (ha f hf).add (hb f hf)
  · intro a b _ _ ha hb f hf
    rw [mul_assoc]
    exact ha _ (hb f hf)

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.Fo.fockEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Ops F) (s : Set (S4 F)), s.Finite → (∀ φ ∈ s, φ ∈ Fock D.δ) → ∃ Λ m, ∀ φ ∈ s, φ ∈ O.Fk (Vac D.δ ⊓ Fix D.δ Λ) m := by
  intro F E _ _ _ _ _ _ _ D O s hs
  have hgauss : ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
      PF D.δ O (fun v => gauss D.δ v * g (finPartPi v)) := by
    intro g hg
    let φ₀ : S4 F := ⟨_, gaussMem F E D g hg⟩
    obtain ⟨Λ, hΛ⟩ := (fixEx F D.δ).1 φ₀
    have hV : φ₀ ∈ Vac D.δ := by
      intro v v' e
      change (gauss D.δ v * g (finPartPi v)) * gauss D.δ v' = (gauss D.δ v' * g (finPartPi v')) * gauss D.δ v
      rw [e]
      ring
    exact ⟨Λ, 0, φ₀, ⟨hV, hΛ⟩, rfl⟩
  have hfock : ∀ φ ∈ Fock D.δ, PF D.δ O φ.1 := by
    intro φ hφ
    have hφ' : φ.1 ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F), ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
        φ = fun v => p v * gauss D.δ v * g (finPartPi v)} := hφ
    refine Submodule.span_induction (p := fun f _ => PF D.δ O f) ?_ (PF.zero _ _) ?_ ?_ hφ'
    · rintro _ ⟨p, hp, g, hg, rfl⟩
      have := PF.poly hp _ (hgauss g hg)
      convert this using 1
      ext v
      simp [mul_assoc]
    · intro a b _ _ ha hb
      exact ha.add hb
    · intro c a _ ha
      exact ha.smul c
  induction s, hs using Set.Finite.induction_on with
  | empty => exact fun _ => ⟨⊤, 0, fun φ h => absurd h (Set.notMem_empty φ)⟩
  | @insert a s _ _ ih =>
    intro h
    obtain ⟨Λ, m, hm⟩ := ih fun φ hφ => h φ (Set.mem_insert_of_mem _ hφ)
    obtain ⟨Λ', m', φ, hφ, e⟩ := hfock a (h a (Set.mem_insert _ _))
    obtain rfl : φ = a := Subtype.ext e
    refine ⟨Λ ⊓ Λ', max m m', ?_⟩
    rintro ψ' (rfl | hψ)
    · exact fk_mono inf_le_right (le_max_right _ _) hφ
    · exact fk_mono inf_le_left (le_max_left _ _) (hm ψ' hψ)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OmFinite
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.omFinite :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (φ : S4 F) (C : Set (G1 F)), IsCompact C → ∃ s : Set (G1 F), s.Finite ∧ (∀ g ∈ s, InfOne g) ∧
    ∀ k ∈ C, ∃ g ∈ s, ∃ k', FinOne k' ∧ (InfOrth k → InfOrth k') ∧ W.Om k φ = W.Om k' (W.Om g φ) := by
  intro F E _ _ _ _ _ _ _ D W φ C hC
  obtain ⟨pi, pf, hpf, hp⟩ := UpperTheory.ConvolutionTheory.R2.Fo.proj F
  have hU : ∀ k₀ ∈ C, {k | W.Om (pf k) φ = W.Om (pf k₀) φ} ∈ 𝓝 k₀ := by
    intro k₀ _
    have hc : Continuous fun k : G1 F => pf (k₀⁻¹ * k) :=
      hpf.comp (continuous_const.mul continuous_id)
    have h1 : Tendsto (fun k : G1 F => pf (k₀⁻¹ * k)) (𝓝 k₀) (𝓝 1) := by
      have h := hc.tendsto k₀
      simpa using h
    filter_upwards [h1.eventually (W.level φ)] with k hk
    have h2 := hk (hp _).2.1
    have h3 : pf k = pf k₀ * pf (k₀⁻¹ * k) := by rw [← map_mul, mul_inv_cancel_left]
    change W.Om (pf k) φ = W.Om (pf k₀) φ
    rw [h3, map_mul, Module.End.mul_apply, h2]
  obtain ⟨t, -, hcov⟩ := hC.elim_nhds_subcover _ hU
  refine ⟨pf '' (t : Set (G1 F)), t.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact (hp k).2.1
  · intro k hk
    obtain ⟨k₀, hk₀, hkk⟩ := Set.mem_iUnion₂.1 (hcov hk)
    refine ⟨pf k₀, ⟨k₀, hk₀, rfl⟩, pi k, (hp k).1, ?_, ?_⟩
    · intro ho i j
      have e : ∀ a b, ((pi k).1 a b).1 = (k.1 a b).1 := (hp k).2.2.2.1
      have key : (((pi k).1 * (pi k).1ᵀ) i j).1 = ((k.1 * k.1ᵀ) i j).1 := by
        have hadd : ∀ a b c d : A F, (a * b + c * d).1 = a.1 * b.1 + c.1 * d.1 := fun _ _ _ _ => rfl
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
        rw [hadd, hadd, e i 0, e j 0, e i 1, e j 1]
      exact key.trans (ho i j)
    · have h4 : W.Om k = W.Om (pi k) * W.Om (pf k) := by rw [← map_mul, (hp k).2.2.1]
      rw [h4, Module.End.mul_apply]
      exact congrArg _ hkk
end

