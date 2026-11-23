module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0002
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Decomp
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

section Alg
variable {R : Type} [CommRing R]

private def pe (e : R) (he : e * e = e) : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 2) (Fin 2) R where
  toFun M := 1 + e • (M - 1)
  map_one' := by simp
  map_mul' A B := by
    obtain ⟨X, rfl⟩ : ∃ X, A = 1 + X := ⟨A - 1, by abel⟩
    obtain ⟨Y, rfl⟩ : ∃ Y, B = 1 + Y := ⟨B - 1, by abel⟩
    have h1 : (1 + X) * (1 + Y) - 1 = X + Y + X * Y := by noncomm_ring
    change 1 + e • ((1 + X) * (1 + Y) - 1) = (1 + e • (1 + X - 1)) * (1 + e • (1 + Y - 1))
    rw [h1, add_sub_cancel_left, add_sub_cancel_left]
    simp only [smul_add, mul_add, add_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, he]
    abel

private theorem pe_val (e : R) (he : e * e = e) (M : Matrix (Fin 2) (Fin 2) R) :
    pe e he M = 1 + e • (M - 1) := rfl

private theorem idem_compl (e : R) (he : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  linear_combination he

private theorem comm0 (c : R) (X Y : Matrix (Fin 2) (Fin 2) R) (h : c • Y = 0) :
    Commute (1 + c • X) (1 + Y) := by
  have h1 : (c • X) * Y = 0 := by rw [Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_zero]
  have h2 : Y * (c • X) = 0 := by rw [Matrix.mul_smul, ← Matrix.smul_mul, h, Matrix.zero_mul]
  change _ * _ = _ * _
  simp only [mul_add, add_mul, one_mul, mul_one, h1, h2]
  abel

private theorem split (e : R) (he : e * e = e) (M : Matrix (Fin 2) (Fin 2) R) :
    M = pe (1 - e) (idem_compl e he) M * pe e he M := by
  obtain ⟨X, rfl⟩ : ∃ X, M = 1 + X := ⟨M - 1, by abel⟩
  have h0 : (1 - e) * e = 0 := by linear_combination -he
  have h1 : ((1 - e) • X) * (e • X) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h0, zero_smul]
  have e1 : pe (1 - e) (idem_compl e he) (1 + X) = 1 + (1 - e) • X := by
    rw [pe_val, add_sub_cancel_left]
  have e2 : pe e he (1 + X) = 1 + e • X := by rw [pe_val, add_sub_cancel_left]
  rw [e1, e2]
  simp only [mul_add, add_mul, one_mul, mul_one, h1]
  rw [sub_smul, one_smul]
  abel

end Alg

section Ad
variable {E : Type} [Field E] [NumberField E]

private theorem fin_of_inf (g : GL (Fin 2) (A E))
    (hg : ∀ i j, (g.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1) :
    g = finGL E 2 (Matrix.GeneralLinearGroup.map (pFin E) g) := by
  have h1 := map_cornerGL_of_zero (sFin E) (RingHom.fst (InfiniteAdeleRing E) (Af E)) (fun _ => rfl)
    (Matrix.GeneralLinearGroup.map (pFin E) g)
  have h2 := pFin_finGL (E := E) (a := 2) (Matrix.GeneralLinearGroup.map (pFin E) g)
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · have h3 : ((finGL E 2 (Matrix.GeneralLinearGroup.map (pFin E) g)).val i j).1 =
        (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing E)) i j :=
      congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing E) => x.val i j) h1
    rw [hg, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · exact (congrArg (fun x : GL (Fin 2) (Af E) => x.val i j) h2).symm

end Ad

section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem two_ne (v : P F) : (2 : Kv v) ≠ 0 := by
  intro h
  have h' : algebraMap F (Kv v) 2 = 0 := by rw [map_ofNat]; exact h
  exact two_ne_zero ((map_eq_zero _).1 h')

private theorem sg_zero (v : P F) : sg v 0 = 0 := by
  obtain ⟨hadd, -⟩ := sgLaws F v
  have := hadd 0 0
  simpa using this

private theorem mk_zero (D : Dat F E) : D.mkE 0 0 = 0 := by simp [Dat.mkE]

private theorem pm (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (a b c d : Kv v) :
    D.mkE (sg v a) (sg v b) * D.mkE (sg v c) (sg v d) =
      D.mkE (sg v (a * c + θ ^ 2 * (b * d))) (sg v (a * d + b * c)) := by
  obtain ⟨hmul, -⟩ := mkLaws F E D
  obtain ⟨hadd, hsm, hcp, -⟩ := sgLaws F v
  have hr : cp v (rt D.δ) = θ ^ 2 := by rw [hθ]; rfl
  rw [hmul, hadd, hadd]
  simp only [hsm, hcp, hr]

private noncomputable def ee (D : Dat F E) (v : P F) (θ : Kv v) : A E := D.mkE (sg v (1 / 2)) (sg v (-(1 / (2 * θ))))

private theorem ee_idem (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) :
    ee D v θ * ee D v θ = ee D v θ := by
  have h2 := two_ne v
  rw [ee, pm D v θ hθ]
  congr 2
  · field_simp; ring
  · field_simp; ring

private theorem ee_sE (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (k : Kv v) :
    ee D v θ * sE D v θ k = 0 := by
  have h2 := two_ne v
  rw [ee, sE, pm D v θ hθ]
  have e1 : (1 / 2 * (k / 2) + θ ^ 2 * (-(1 / (2 * θ)) * (k / (2 * θ))) : Kv v) = 0 := by field_simp; ring
  have e2 : (1 / 2 * (k / (2 * θ)) + -(1 / (2 * θ)) * (k / 2) : Kv v) = 0 := by field_simp; ring
  rw [e1, e2, sg_zero, mk_zero]

private theorem squareRoot_idempotent_embed (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (s : Kv v) :
    ee D v θ * D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))) = D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))) := by
  have h2 := two_ne v
  rw [ee, pm D v θ hθ]
  congr 2
  · field_simp; ring
  · field_simp; ring

private theorem ee_fst (D : Dat F E) (v : P F) (θ : Kv v) : (ee D v θ).1 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hs, -, -⟩ := sgLaws F v
  have h : ∀ x, (AdeleBaseChange.adeleMap F E (sg v x)).1 = 0 := fun x => by
    change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = 0
    rw [(hs x).1, map_zero]
  change (AdeleBaseChange.adeleMap F E _).1 + (AdeleBaseChange.adeleMap F E _).1 * (rt D.θ).1 = 0
  rw [h, h, zero_mul, add_zero]

end Main

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.decomp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (v : P F) (θ : Kv v) (J : GLv v →* GL (Fin 2) (A E)), Splt D v θ J → ∀ h : GL (Fin 2) (A E),
      ∃ h' k, h = h' * finGL E 2 k ∧ (∀ s, Commute h' (nbar D v θ s)) ∧ ∀ x, Commute (finGL E 2 k) (J x) := by
  intro F E _ _ _ _ _ _ D v θ J hs h
  have he := ee_idem D v θ hs.sq hs.ne
  obtain ⟨k, hk⟩ : ∃ k, Units.map (pe (ee D v θ) he) h = finGL E 2 k := by
    refine ⟨_, fin_of_inf _ fun i j => ?_⟩
    change ((1 + ee D v θ • (h.val - 1) : Matrix (Fin 2) (Fin 2) (A E)) i j).1 = _
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    change ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1 + (ee D v θ).1 * _ = _
    rw [ee_fst, zero_mul, add_zero]
  refine ⟨Units.map (pe (1 - ee D v θ) (idem_compl _ he)) h, k, ?_, fun s => ?_, fun x => ?_⟩
  · rw [← hk]
    exact Units.ext (split _ he h.val)
  · have hn : (nbar D v θ s).val = 1 + !![0, D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))); 0, 0] := by
      ext i j
      change (!![1, D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))); 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j = _
      fin_cases i <;> fin_cases j <;> simp
    have hz := squareRoot_idempotent_embed D v θ hs.sq hs.ne s
    refine Units.ext ?_
    have := comm0 (1 - ee D v θ) (h.val - 1) !![0, D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))); 0, 0] (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sub_mul, hz])
    rw [← hn] at this
    exact this.eq
  · rw [← hk]
    have hj : (J x).val = 1 + Matrix.of fun i j => sE D v θ (x.val i j - (1 : M2 v) i j) := by
      ext i j
      rw [hs.val]; rfl
    refine Units.ext ?_
    have := comm0 (ee D v θ) (h.val - 1) (Matrix.of fun i j => sE D v θ (x.val i j - (1 : M2 v) i j)) (by
      ext i j
      simp [ee_sE D v θ hs.sq hs.ne])
    rw [← hj] at this
    exact this.eq
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IndicatorMemSB
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : f ∈ SB X)
    {U : Set X} (hU : IsClopen U) : U.indicator f ∈ SB X := by
  refine ⟨?_, ?_⟩
  · have h1 : IsLocallyConstant (U.indicator fun _ : X => (1 : ℂ)) := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro c
      by_cases h1 : (1 : ℂ) = c <;> by_cases h0 : (0 : ℂ) = c
      · exact absurd (h1.trans h0.symm) one_ne_zero
      · have : (U.indicator fun _ : X => (1 : ℂ)) ⁻¹' {c} = U := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, h1, Ne.symm h0, h0]
        rw [this]; exact hU.isOpen
      · have : (U.indicator fun _ : X => (1 : ℂ)) ⁻¹' {c} = Uᶜ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, Ne.symm h1, h1, h0]
        rw [this]; exact hU.compl.isOpen
      · have : (U.indicator fun _ : X => (1 : ℂ)) ⁻¹' {c} = ∅ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, Ne.symm h1, Ne.symm h0, h1, h0]
        rw [this]; exact isOpen_empty
    have h2 : U.indicator f = (U.indicator fun _ : X => (1 : ℂ)) * f := by
      ext x
      by_cases hx : x ∈ U <;> simp [hx]
    rw [h2]
    exact h1.mul hf.1
  · exact HasCompactSupport.mono hf.2 (fun x hx => by
      by_contra h0
      apply hx
      have h0' : f x = 0 := by simpa using h0
      by_cases hxU : x ∈ U <;> simp [hxU, h0'])

theorem UpperTheory.ConvolutionTheory.R2.I.loc :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (ℓ : SB (M2 v) →ₗ[ℂ] ℂ),
      (∀ (s : Kv v) (a a' : SB (M2 v)), (∀ m, a'.1 m = ψl v (-(s * m.det)) * a.1 m) → ℓ a' = ψl v (-s) * ℓ a) →
      ∀ a : SB (M2 v), (∀ m : M2 v, m.det = 1 → a.1 m = 0) → ℓ a = 0 := by
  intro F _ _ v ℓ h a ha
  obtain ⟨-, -, hadd, hlc, hnt, -⟩ := psiLaws F v
  have hψ0 : ∀ x, ψl v x ≠ 0 := fun x => Circle.coe_ne_zero _

  have key : ∀ m0 : M2 v, m0.det ≠ 1 → ∃ N : Set (M2 v), IsClopen N ∧ m0 ∈ N ∧
      ∀ b : SB (M2 v), Function.support b.1 ⊆ N → ℓ b = 0 := by
    intro m0 hm
    obtain ⟨t, ht⟩ := hnt (m0.det - 1) (sub_ne_zero.mpr hm)
    have hz : ψl v (-(-t * m0.det)) ≠ ψl v (- -t) := by
      intro hzz
      apply ht
      have e : -(-t * m0.det) = t * (m0.det - 1) + - -t := by ring
      rw [e, hadd] at hzz
      exact mul_right_cancel₀ (hψ0 _) (hzz.trans (one_mul _).symm)
    have hf : IsLocallyConstant (fun m : M2 v => ψl v (-(-t * m.det))) :=
      hlc.comp_continuous (by
        have : Continuous fun m : M2 v => m.det := continuous_id.matrix_det
        exact (continuous_const.mul this).neg)
    refine ⟨(fun m : M2 v => ψl v (-(-t * m.det))) ⁻¹' {ψl v (-(-t * m0.det))},
      hf.isClopen_fiber _, rfl, fun b hb => ?_⟩
    have h1 := h (-t) b (ψl v (-(-t * m0.det)) • b) (fun m => by
      by_cases hm' : b.1 m = 0
      · simp [hm']
      · have : ψl v (-(-t * m.det)) = ψl v (-(-t * m0.det)) := hb hm'
        rw [this]; rfl)
    rw [map_smul, smul_eq_mul] at h1
    by_contra hne
    exact hz (mul_right_cancel₀ hne h1)
  have hsupp : tsupport a.1 = Function.support a.1 := by
    refine IsClosed.closure_eq ?_
    have : Function.support a.1 = (a.1 ⁻¹' {0})ᶜ := by
      ext x; simp
    rw [this]
    exact (a.2.1.isClopen_fiber 0).compl.isClosed
  have main : ∃ C : Set (M2 v), IsClopen C ∧ tsupport a.1 ⊆ C ∧
      ∀ b : SB (M2 v), Function.support b.1 ⊆ C → ℓ b = 0 := by
    refine IsCompact.induction_on (p := fun T : Set (M2 v) => ∃ C : Set (M2 v), IsClopen C ∧ T ⊆ C ∧
      ∀ b : SB (M2 v), Function.support b.1 ⊆ C → ℓ b = 0) a.2.2 ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, subset_rfl, fun b hb => ?_⟩
      have : b = 0 := by
        apply Subtype.ext
        funext x
        by_contra hx
        exact hb hx
      rw [this, map_zero]
    · rintro S T hST ⟨C, hC, hTC, hb⟩
      exact ⟨C, hC, hST.trans hTC, hb⟩
    · rintro S T ⟨C, hC, hSC, hb⟩ ⟨C', hC', hTC', hb'⟩
      refine ⟨C ∪ C', hC.union hC', Set.union_subset_union hSC hTC', fun b hbs => ?_⟩
      have e : b = ⟨C.indicator b.1, indicator_mem_SB b.2 hC⟩ + ⟨Cᶜ.indicator b.1, indicator_mem_SB b.2 hC.compl⟩ := by
        apply Subtype.ext
        funext x
        by_cases hx : x ∈ C <;> simp [hx]
      rw [e, map_add (f := _), hb _ (fun x hx => by by_contra hc; exact hx (by simp [hc])), hb', add_zero]
      intro x hx
      have hxC : x ∉ C := by
        intro hc
        exact hx (by simp [hc])
      have hxb : b.1 x ≠ 0 := by
        intro h0
        apply hx
        simp [h0]
      exact (hbs hxb).resolve_left hxC
    · intro x hx
      rw [hsupp] at hx
      have hdet : x.det ≠ 1 := fun h1 => hx (ha x h1)
      obtain ⟨N, hN, hxN, hb⟩ := key x hdet
      exact ⟨N, mem_nhdsWithin_of_mem_nhds (hN.isOpen.mem_nhds hxN), N, hN, subset_rfl, hb⟩
  obtain ⟨C, -, hC, hb⟩ := main
  exact hb a (subset_tsupport _ |>.trans hC)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.JmMeasurable
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] {v : P F}

private noncomputable def Jm (c : Fin 2 → Kv v) : Fin 2 → Kv v := ![-c 1, c 0]

private lemma Jm_Jm (c : Fin 2 → Kv v) : Jm (Jm c) = -c := by
  funext i; fin_cases i <;> simp [Jm]

private lemma Jm_measurable : Measurable (Jm (v := v)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · have h : Measurable fun c : Fin 2 → Kv v => -c 1 := measurable_neg.comp (measurable_pi_apply (1 : Fin 2))
    simpa [Jm] using h
  · simpa [Jm] using measurable_pi_apply (0 : Fin 2)

private noncomputable def JmE : (Fin 2 → Kv v) ≃ᵐ (Fin 2 → Kv v) where
  toFun := Jm
  invFun := fun c => -Jm c
  left_inv := fun c => by
    show -Jm (Jm c) = c
    rw [Jm_Jm, neg_neg]
  right_inv := fun c => by
    show Jm (-Jm c) = c
    funext i; fin_cases i <;> simp [Jm]
  measurable_toFun := Jm_measurable
  measurable_invFun := measurable_neg.comp Jm_measurable

private lemma Jm_mp : MeasurePreserving (Jm (v := v)) (μ2 v) (μ2 v) := by
  have hs := measurePreserving_piCongrLeft (α := fun _ : Fin 2 => Kv v)
    (fun _ => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) (Equiv.swap (0 : Fin 2) 1)
  have hn := measurePreserving_pi (fun _ : Fin 2 => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v))
    (fun _ : Fin 2 => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v))
    (f := fun (i : Fin 2) (x : Kv v) => if i = 0 then -x else x) (by
      intro i
      fin_cases i
      · simpa using Measure.measurePreserving_neg _
      · convert MeasurePreserving.id (GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) using 1
        funext x
        simp)
  have h := hn.comp hs
  have hf : Jm (v := v) = (fun (a : Fin 2 → Kv v) (i : Fin 2) => if i = 0 then -a i else a i) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Kv v) (Equiv.swap (0 : Fin 2) 1)) := by
    funext c i
    fin_cases i <;> simp [Jm, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hf]
  exact h

private lemma cols_col (c c' : Fin 2 → Kv v) : (fun i => cols c c' i 1) = c' := by
  funext i; fin_cases i <;> simp [cols]

private lemma sw_cols (p q : Fin 2 → Kv v) : sw (cols p q) = cols q p := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sw, cols]

private lemma sw_sw (m : M2 v) : sw (sw m) = m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sw]

private lemma eq_cols (m : M2 v) : m = cols (fun i => m i 0) (fun i => m i 1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cols]

private lemma sw_continuous : Continuous (sw (v := v)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [sw] <;> fun_prop

private noncomputable def swH : M2 v ≃ₜ M2 v where
  toFun := sw
  invFun := sw
  left_inv := sw_sw
  right_inv := sw_sw
  continuous_toFun := sw_continuous
  continuous_invFun := sw_continuous

private lemma comp_sw_mem {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) : (fun X => a (sw X)) ∈ SB (M2 v) :=
  ⟨ha.1.comp_continuous sw_continuous, ha.2.comp_homeomorph swH⟩

private lemma slice_mem {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) (c : Fin 2 → Kv v) :
    (fun c' => a (cols c c')) ∈ localSchwartzBruhatPi (Kv v) (ι := Fin 2) := by
  have hc : Continuous fun c' : Fin 2 → Kv v => cols c c' := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [cols] <;> fun_prop
  have hr : Continuous fun X : M2 v => (fun i => X i 1 : Fin 2 → Kv v) := by
    refine continuous_pi fun i => ?_
    exact (continuous_id.matrix_elem i 1)
  have he : IsClosedEmbedding fun c' : Fin 2 → Kv v => cols c c' :=
    Function.LeftInverse.isClosedEmbedding (f := fun X : M2 v => (fun i => X i 1 : Fin 2 → Kv v))
      (fun c' => cols_col c c') hr hc
  exact ⟨ha.1.comp_continuous hc, ha.2.comp_isClosedEmbedding he⟩

private lemma Pt_cols (a : M2 v → ℂ) (c₁ c : Fin 2 → Kv v) :
    Pt a (cols c₁ c) = localFourierPi (localAdelicChar F v) (fun c' => a (cols c c')) (Jm c₁) := by
  simp only [Pt, localFourierPi, cols_col]
  unfold μ2
  refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
  have h : c₁ 0 * c' 1 - c₁ 1 * c' 0 = ∑ i, c' i * Jm c₁ i := by
    simp [Jm, Fin.sum_univ_two]; ring
  simp only [ψl]
  rw [← h]
  simp [cols]

private lemma fourier_rot (G : (Fin 2 → Kv v) → ℂ) (q : Fin 2 → Kv v) :
    localFourierPi (localAdelicChar F v) (fun c => G (Jm c)) (Jm q) =
      localFourierPi (localAdelicChar F v) G (-q) := by
  have h := (Jm_mp (v := v)).integral_comp (JmE (v := v)).measurableEmbedding
    (fun y => G y * ((localAdelicChar F v (∑ i, y i * (-q) i) : Circle) : ℂ))
  change ∫ x, G (Jm x) * ((localAdelicChar F v (∑ i, x i * Jm q i) : Circle) : ℂ) ∂(μ2 v) =
    ∫ y, G y * ((localAdelicChar F v (∑ i, y i * (-q) i) : Circle) : ℂ) ∂(μ2 v)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  have : ∑ i, c i * Jm q i = ∑ i, Jm c i * (-q) i := by
    simp [Jm, Fin.sum_univ_two]
  simp only [this]

private lemma part1 {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) (p q : Fin 2 → Kv v) :
    Pt (fun X => Pt a (sw X)) (cols q p) = a (cols p q) := by
  have hc := continuous_localAdelicChar (K := F) v
  have hn : localAdelicChar F v ≠ 1 := localAdelicChar_ne_one v
  have hb := slice_mem ha p
  have hG := localFourierPi_mem hc hn hb
  rw [Pt_cols]
  have h1 : (fun c' => Pt a (sw (cols p c'))) =
      fun c' => localFourierPi (localAdelicChar F v) (fun c'' => a (cols p c'')) (Jm c') := by
    funext c'
    rw [sw_cols, Pt_cols]
  rw [h1, fourier_rot, localFourierPi_localFourierPi hc hn hb]
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.ptInv :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∀ a ∈ SB (M2 v), (∀ m, Pt (fun X => Pt a (sw X)) (sw m) = a m) ∧ ∃ a' ∈ SB (M2 v), Pt a' = a := by
  intro F _ _ v a ha
  have h1 : ∀ b ∈ SB (M2 v), ∀ m, Pt (fun X => Pt b (sw X)) (sw m) = b m := by
    intro b hb m
    rw [eq_cols m, sw_cols]
    exact part1 hb _ _
  refine ⟨h1 a ha, ?_⟩
  obtain ⟨T, hT⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have hb := comp_sw_mem ha
  have hTb : Pt (fun X => a (sw X)) ∈ SB (M2 v) := by
    have := (T ⟨_, hb⟩).2
    rwa [hT] at this
  refine ⟨fun X => Pt (fun Y => a (sw Y)) (sw X), comp_sw_mem hTb, ?_⟩
  funext m
  have := h1 _ hb (sw m)
  rw [sw_sw] at this
  simpa [sw_sw] using this
end

