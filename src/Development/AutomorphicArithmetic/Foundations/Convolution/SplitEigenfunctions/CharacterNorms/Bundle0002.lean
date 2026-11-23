module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NzCont
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Nz

variable {E : Type} [Field E] [NumberField E]

theorem cont_sInf : Continuous (TR.sInf ℚ) :=
  (TR.continuous_infEq ℚ).prodMk continuous_const

theorem cont_rotval : Continuous fun t : ℝ => (rot t).val := by
  refine continuous_matrix fun i j => ?_
  have e : ∀ t, (rot t).val i j = (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j - TR.sInf ℚ ((1 : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) i j) +
      TR.sInf ℚ ((X t).val i j) := by
    intro t
    rw [rot_eq]
    rfl
  simp only [e]
  refine continuous_const.add (cont_sInf.comp ?_)
  refine continuous_pi fun w => ?_
  fin_cases i <;> fin_cases j <;> simp [X] <;> fun_prop

theorem rot_neg (t : ℝ) : rot (-t) = (rot t)⁻¹ := by
  rw [rot_eq, rot_eq, X_neg, map_inv]

theorem cont_rot : Continuous rot := by
  refine Units.continuous_iff.2 ⟨cont_rotval, ?_⟩
  have e : (fun t => ((rot t)⁻¹).val) = (fun t => (rot t).val) ∘ Neg.neg := by
    funext t
    simp [rot_neg]
  change Continuous fun t => ((rot t)⁻¹).val
  rw [e]
  exact cont_rotval.comp continuous_neg

theorem cont_em : Continuous (em E) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id AdeleBaseChange.continuous_adeleMap)

theorem contOn_iy : ContinuousOn iy ({0}ᶜ : Set ℝ) := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have e : (fun y : ({0}ᶜ : Set ℝ) => ((iy y : (A ℚ)ˣ) : A ℚ)) = fun y : ({0}ᶜ : Set ℝ) => 1 - TR.sInf ℚ 1 + TR.sInf ℚ fun _ => (y : ℝ) := by
      funext y
      exact iy_coe y.2
    change Continuous fun y : ({0}ᶜ : Set ℝ) => ((iy y : (A ℚ)ˣ) : A ℚ)
    rw [e]
    refine continuous_const.add (cont_sInf.comp ?_)
    exact continuous_pi fun _ => continuous_subtype_val
  · have e : (fun y : ({0}ᶜ : Set ℝ) => (((iy y)⁻¹ : (A ℚ)ˣ) : A ℚ)) = fun y : ({0}ᶜ : Set ℝ) => 1 - TR.sInf ℚ 1 + TR.sInf ℚ fun _ => (y : ℝ)⁻¹ := by
      funext y
      exact iy_inv_coe y.2
    change Continuous fun y : ({0}ᶜ : Set ℝ) => (((iy y)⁻¹ : (A ℚ)ˣ) : A ℚ)
    rw [e]
    refine continuous_const.add (cont_sInf.comp ?_)
    refine continuous_pi fun _ => ?_
    exact continuous_subtype_val.inv₀ fun y => y.2

theorem contOn_curve : ContinuousOn (fun p : ℝ × ℝ => em E (aE (iy p.1) * rot p.2)) (({0}ᶜ : Set ℝ) ×ˢ Set.univ) := by
  refine cont_em.comp_continuousOn (ContinuousOn.mul (continuous_aE.comp_continuousOn ?_) (cont_rot.comp continuous_snd).continuousOn)
  exact contOn_iy.comp continuous_fst.continuousOn fun p hp => hp.1

theorem cont_n : Continuous fun q : A E => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [nU] <;> fun_prop
  · have e : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, nU_zero, gl_one])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [nU] <;> fun_prop

theorem cont_psi : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar

theorem cont_mkE (D : Dat ℚ E) : Continuous fun x : Fin 2 → A ℚ => nE D x :=
  cont_n.comp ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
    ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const))

theorem adelic_measure_fundamental_domain_pi_rat_lt_top : adeleMeasurePi ℚ (FS2 ℚ) < ⊤ := by
  obtain ⟨B, hB, hEB⟩ : ∃ B, IsCompact B ∧ fundamentalSet ℚ ⊆ B :=
    ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
      (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  have hC : IsCompact (Set.univ.pi fun _ : Fin 2 => B) := isCompact_univ_pi fun _ => hB
  exact (measure_mono (show FS2 ℚ ⊆ Set.univ.pi fun _ : Fin 2 => B from fun x hx i hi => hEB (hx i hi))).trans_lt hC.measure_lt_top

theorem cont_Wo (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} (hφ : Continuous φ) (hb : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B)
    {T : Type} [TopologicalSpace T] [FirstCountableTopology T] {c : T → GL (Fin 2) (A E)} (hc : Continuous c) :
    Continuous fun x => Wo D φ (c x) := by
  obtain ⟨B, hB⟩ := hb
  haveI : IsFiniteMeasure ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := ⟨by simpa using adelic_measure_fundamental_domain_pi_rat_lt_top⟩
  have hnorm : ∀ x : A ℚ, ‖ψ x‖ = 1 := fun x => Circle.norm_coe _
  refine continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const _) ?_
  · intro x
    exact ((hφ.comp ((cont_mkE D).mul continuous_const)).mul (cont_psi.comp (continuous_apply 1))).aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, hnorm, mul_one]
    exact hB _
  · refine Filter.Eventually.of_forall fun u => ?_
    exact (hφ.comp (continuous_const.mul hc)).mul continuous_const

theorem contOn_Wo (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} (hφ : Continuous φ) (hb : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B) :
    ContinuousOn (fun p : ℝ × ℝ => Wo D φ (em E (aE (iy p.1) * rot p.2))) (({0}ᶜ : Set ℝ) ×ˢ Set.univ) := by
  rw [continuousOn_iff_continuous_restrict]
  exact cont_Wo D hφ hb (continuousOn_iff_continuous_restrict.1 contOn_curve)

end UpperTheory.ConvolutionTheory.RankTwoDescent.Nz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.TrTranslate
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Nz

variable {E : Type} [Field E] [NumberField E]

def FinOne (h : GL (Fin 2) (A E)) : Prop := ∀ i j, (h.val i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).2

def InfOneG (m : GL (Fin 2) (A E)) : Prop := ∀ i j, (m.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1

theorem comm_of {h m : GL (Fin 2) (A E)} (hf : FinOne h) (hi : InfOneG m) : m * h = h * m := by
  let f1 : A E →+* InfiniteAdeleRing E := RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
  let f2 : A E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
  have hm : f1.mapMatrix m.val = 1 := by
    rw [← map_one f1.mapMatrix]
    exact Matrix.ext fun i j => hi i j
  have hh : f2.mapMatrix h.val = 1 := by
    rw [← map_one f2.mapMatrix]
    exact Matrix.ext fun i j => hf i j
  have e1 : f1.mapMatrix (m * h).val = f1.mapMatrix (h * m).val := by
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hm, one_mul, mul_one]
  have e2 : f2.mapMatrix (m * h).val = f2.mapMatrix (h * m).val := by
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hh, one_mul, mul_one]
  exact Units.ext (Matrix.ext fun i j => Prod.ext (congrFun (congrFun e1 i) j) (congrFun (congrFun e2 i) j))

theorem hU_fin (D : Dat ℚ E) (u : ℝ) : (D.mkE 0 (bI u)).2 = 0 := by
  change (AdeleBaseChange.adeleMap ℚ E 0).2 + (AdeleBaseChange.adeleMap ℚ E (bI u)).2 * (rt D.θ : A E).2 = 0
  have h : (AdeleBaseChange.adeleMap ℚ E (bI u)).2 = 0 := by
    change AdeleBaseChange.finiteAdeleMap ℚ E (bI u).2 = 0
    rw [bI_snd, map_zero]
  rw [h, map_zero, zero_mul]
  exact add_zero _

theorem finOne_hU (D : Dat ℚ E) (u : ℝ) : FinOne (hU D u) := by
  intro i j
  have h := hU_fin D u
  fin_cases i <;> fin_cases j <;> simp [hU, nE, gl, SpecialLinearGroup.toGL, nU, h]

theorem infOne_em {k : GL (Fin 2) (A ℚ)} (h : ∀ i j, (k.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1) :
    InfOneG (em E k) := by
  intro i j
  have e : ((em E k).val i j) = AdeleBaseChange.adeleMap ℚ E (k.val i j) := rfl
  have e2 : (AdeleBaseChange.adeleMap ℚ E (k.val i j)).1 = (AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)).1 := by
    rw [AdeleBaseChange.adeleMap_apply, AdeleBaseChange.adeleMap_apply, h]
  rw [e, e2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

variable [_root_.NumberField.IsTotallyComplex E]

theorem exists_X (D : Dat ℚ E) (u : ℝ) : ∃ X, infGL E 2 X = hU D u := by
  set z := D.mkE 0 (bI u) with hz
  have hz2 : z.2 = 0 := hU_fin D u
  have hs : sInf E (GlobalTheory.CuspRep.pInf E z) = z := Prod.ext ((infEq E).apply_symm_apply _) hz2.symm
  refine ⟨⟨!![1, GlobalTheory.CuspRep.pInf E z; 0, 1], !![1, -GlobalTheory.CuspRep.pInf E z; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, Units.ext ?_⟩
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) (A E)) i j - sInf E ((1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j) + sInf E (!![1, GlobalTheory.CuspRep.pInf E z; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [hU, nE, gl, SpecialLinearGroup.toGL, nU, ← hz, hs]

theorem Tr_translate {P : CuspSub E 2} {φ : GL (Fin 2) (A E) → ℂ} (h : φ ∈ Tr P) (x : GL (Fin 2) (A E)) :
    (fun g => φ (g * x)) ∈ Tr P := by
  unfold Tr at h ⊢
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨f', hf', y, rfl⟩ := hf
    exact Submodule.subset_span ⟨f', hf', x * y, by funext g; simp [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem Gd_translate {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {φ : GL (Fin 2) (A E) → ℂ} (hG : Gd D P L N φ) (u : ℝ) :
    Gd D P L N (fun g => φ (g * hU D u)) := by
  obtain ⟨X, hX⟩ := exists_X D u
  have hc : ∀ k, finGL E 2 k * hU D u = hU D u * finGL E 2 k := by
    intro k
    rw [← hX, infGL_comm]
  refine ⟨hG.pos, hG.dvd, hG.same, Tr_translate hG.mem _, hG.pl, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨h1, B, hB, hE⟩ := hG.fix w hw
    refine ⟨?_, B, hB, ?_⟩
    · intro g k hk
      have e : H.lc w k = finGL E 2 (locGL E 2 w k) := rfl
      change φ (g * H.lc w k * hU D u) = φ (g * hU D u)
      rw [e, mul_assoc, hc, ← mul_assoc, ← e]
      exact h1 _ k hk
    · intro g
      have e : (fun y => φ (g * finGL E 2 (locGL E 2 w y) * hU D u)) = fun y => φ (g * hU D u * finGL E 2 (locGL E 2 w y)) := by
        funext y
        rw [mul_assoc, hc, ← mul_assoc]
      change UpperTheory.V.Af.Smo.Eig w B fun y => φ (g * finGL E 2 (locGL E 2 w y) * hU D u)
      rw [e]
      exact hE (g * hU D u)
  · intro k hk g
    change φ (g * em E k * hU D u) = φ (g * hU D u)
    rw [mul_assoc, comm_of (finOne_hU D u) (infOne_em hk.1), ← mul_assoc]
    exact hG.lev k hk _
  · intro y x hne v hv
    rw [Wo_right, ← hX, mul_assoc, ← map_mul] at hne
    exact hG.supp y _ hne v hv
  · intro t ht hd y x
    rw [Wo_right, Wo_right, ← hX, mul_assoc, mul_assoc, ← map_mul]
    exact hG.tor t ht hd y _

end UpperTheory.ConvolutionTheory.RankTwoDescent.Nz
end
end

