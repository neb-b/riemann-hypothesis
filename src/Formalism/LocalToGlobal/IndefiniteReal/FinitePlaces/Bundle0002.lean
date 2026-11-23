module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0017
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

theorem hO_add_left (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  unfold hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_add_left (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO
  rw [hO_add_left, mul_add, map_add (f := _)]

theorem symplO_add_right (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO
  rw [hO_add_right, mul_add, map_add (f := _)]

theorem symplO_zero_left (y : WO S T) : symplO S T 0 y = 0 := by
  have h := symplO_add_left S T 0 0 y
  rw [add_zero] at h
  linear_combination -1 * h

theorem symplO_zero_right (x : WO S T) : symplO S T x 0 = 0 := by
  have h := symplO_add_right S T x 0 0
  rw [add_zero] at h
  linear_combination -1 * h

theorem symplO_neg_left (x y : WO S T) : symplO S T (-x) y = -symplO S T x y := by
  have h := symplO_add_left S T x (-x) y
  have h0 : x + -x = 0 := by simp
  rw [h0, symplO_zero_left] at h
  linear_combination -1 * h

theorem symplO_neg_right (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  have h0 : y + -y = 0 := by simp
  rw [h0, symplO_zero_right] at h
  linear_combination -1 * h

abbrev MO : Type := Matrix (Fin T.rank) (Fin S.rank) (AE D)

def hOM (x y : MO S T) : Matrix (Fin S.rank) (Fin S.rank) (AE D) :=
  HMul.hMul (HMul.hMul (HMul.hMul (Brg.GI S) (y.map (cA D))ᵀ) (Brg.GG T)) x

theorem hO_eq_trace (x y : MO S T) : hO S T x y = (hOM S T x y).trace := by
  unfold hO hOM
  simp only [Brg.GI, Brg.GG, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext d; rw [Finset.sum_comm]

theorem cA_trace {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) : cA D M.trace = ((M.map (cA D))ᵀ).trace := by
  rw [Matrix.trace_transpose]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem hO_swap (x y : MO S T) : hO S T y x = cA D (hO S T x y) := by
  have e0 : (y.map (cA D)).map (cA D) = y := by ext i j; simp [cA_cA]
  have e2 : ((hOM S T x y).map (cA D))ᵀ =
      HMul.hMul (HMul.hMul (HMul.hMul (x.map (cA D))ᵀ (Brg.GG T)) y) (Brg.GI S) := by
    unfold hOM
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Brg.GI_herm, Brg.GG_herm, Matrix.transpose_map, e0, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [hO_eq_trace, hO_eq_trace, cA_trace, e2, Matrix.trace_mul_comm]
  unfold hOM
  simp only [Matrix.mul_assoc]

theorem symplO_swap (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [hO_swap S T x y]
  have e : incA D D.host.xi0 * cA D (hO S T x y) = cA D (cA D (incA D D.host.xi0) * hO S T x y) := by
    rw [map_mul, cA_cA]
  rw [e, Brg.trace_cA, Brg.cA_inc, Brg.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem symplOH_add_left (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  unfold symplOH
  rw [symplO_add_left, mul_add]

theorem symplOH_add_right (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  unfold symplOH
  rw [symplO_add_right, mul_add]

theorem symplOH_swap (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH
  rw [symplO_swap, mul_neg]

theorem symplOH_two (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem incA_eq_tmul (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem trace_incA (e : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (incA D e) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  rw [incA_eq_tmul]
  exact Formalism.IndefR.PHeisTh.trace_tmul _

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FiniteAdeleSndAlgebraMap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

section Comp

variable {F : Type} [Field F] [NumberField F]

theorem finite_adele_fst_mul (x y : AF F) : (x * y).1 = x.1 * y.1 := rfl
theorem finite_adele_fst_add (x y : AF F) : (x + y).1 = x.1 + y.1 := rfl
theorem finite_adele_fst_sub (x y : AF F) : (x - y).1 = x.1 - y.1 := rfl
theorem finite_adele_fst_one : (1 : AF F).1 = 1 := rfl
theorem finite_adele_snd_mul (x y : AF F) (v : HeightOneSpectrum (𝓞 F)) : (x * y).2 v = x.2 v * y.2 v := rfl
theorem finite_adele_snd_add (x y : AF F) (v : HeightOneSpectrum (𝓞 F)) : (x + y).2 v = x.2 v + y.2 v := rfl
theorem finite_adele_snd_sub (x y : AF F) (v : HeightOneSpectrum (𝓞 F)) : (x - y).2 v = x.2 v - y.2 v := rfl
theorem finite_adele_snd_one (v : HeightOneSpectrum (𝓞 F)) : (1 : AF F).2 v = 1 := rfl
theorem finite_adele_snd_algebraMap (c : F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (AF F) c).2 v = algebraMap F (v.adicCompletion F) c := rfl

abbrev epv (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (single v 1)

theorem epv_fst (v : HeightOneSpectrum (𝓞 F)) : (epv v).1 = 0 := rfl
theorem epv_self (v : HeightOneSpectrum (𝓞 F)) : (epv v).2 v = 1 := by
  classical
  first
  | exact Pi.single_eq_same v (1 : v.adicCompletion F)
  | (simp [epv, pairA, single]; done)
  | (simp [epv, pairA, single]; convert Pi.single_eq_same v (1 : v.adicCompletion F); done)
  | (simp [epv, pairA, single]; rfl)
theorem epv_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : (epv v).2 w = 0 := by
  classical
  first
  | exact Pi.single_eq_of_ne h (1 : v.adicCompletion F)
  | (simp [epv, pairA, single, h]; done)
  | (simp [epv, pairA, single]; convert Pi.single_eq_of_ne h (1 : v.adicCompletion F); done)
  | (simp [epv, pairA, single]; rfl)

theorem epv_sq (v : HeightOneSpectrum (𝓞 F)) : epv v * epv v = epv v := by
  refine Prod.ext ?_ ?_
  · rw [finite_adele_fst_mul, epv_fst, mul_zero]
  · apply RestrictedProduct.ext
    intro w
    refine (finite_adele_snd_mul (epv v) (epv v) w).trans ?_
    by_cases h : w = v
    · subst h
      rw [epv_self, mul_one]
      exact (epv_self w).symm
    · rw [epv_ne h, mul_zero]
      exact (epv_ne h).symm

end Comp

section Split

variable {D : D7} (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)


include hΔ hδ0 hδ in
theorem exists_splitIdem' (v : HeightOneSpectrum (𝓞 D.host.F)) (s : v.adicCompletion D.host.F)
    (hs : s * s = algebraMap D.host.F (v.adicCompletion D.host.F) Δ) :
    ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) (epv v) := by
  classical
  have hc : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] D.sp.cm.sig x := by
    intro a x
    first
    | rfl
    | simp [cA]
  have h2F : (2 : v.adicCompletion D.host.F) ≠ 0 := by
    have h := (algebraMap D.host.F (v.adicCompletion D.host.F)).injective.ne (two_ne_zero (α := D.host.F))
    rw [map_ofNat, map_zero] at h
    exact h
  have hΔ0 : Δ ≠ 0 := by
    rintro rfl
    apply hδ0
    have h0 : δ * δ = 0 := by rw [← hΔ, map_zero]
    exact mul_self_eq_zero.mp h0
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hΔ0
    have h0 : algebraMap D.host.F (v.adicCompletion D.host.F) Δ = 0 := by rw [← hs, mul_zero]
    exact (map_eq_zero_iff _ (algebraMap D.host.F (v.adicCompletion D.host.F)).injective).mp h0
  have hsv : ∀ t : v.adicCompletion D.host.F, (single v t) v = t := by
    intro t
    first
    | exact Pi.single_eq_same v t
    | (simp [single]; done)
    | (simp [single]; convert Pi.single_eq_same v t; done)
    | (simp [single]; rfl)
  have hsw : ∀ (t : v.adicCompletion D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), w ≠ v →
      (single v t) w = 0 := by
    intro t w hw
    first
    | exact Pi.single_eq_of_ne hw t
    | (simp [single, hw]; done)
    | (simp [single]; convert Pi.single_eq_of_ne hw t; done)
    | (simp [single]; rfl)
  have hAF : ∀ x y : AF D.host.F, x.1 = y.1 → (∀ w, x.2 w = y.2 w) → x = y := by
    intro x y h1 h2
    refine Prod.ext h1 ?_
    apply RestrictedProduct.ext
    exact h2
  obtain ⟨a, ha⟩ : ∃ a : AF D.host.F, a = pairA D.host.F 0 (single v (2 : v.adicCompletion D.host.F)⁻¹) :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : AF D.host.F, b = pairA D.host.F 0 (single v (2 * s)⁻¹) := ⟨_, rfl⟩
  have ha1 : a.1 = 0 := by rw [ha]; rfl
  have hb1 : b.1 = 0 := by rw [hb]; rfl
  have ha2v : a.2 v = (2 : v.adicCompletion D.host.F)⁻¹ := by rw [ha]; exact hsv _
  have hb2v : b.2 v = (2 * s)⁻¹ := by rw [hb]; exact hsv _
  have ha2w : ∀ w, w ≠ v → a.2 w = 0 := by intro w hw; rw [ha]; exact hsw _ w hw
  have hb2w : ∀ w, w ≠ v → b.2 w = 0 := by intro w hw; rw [hb]; exact hsw _ w hw
  let ΔA := algebraMap D.host.F (AF D.host.F) Δ
  have hDAv : ΔA.2 v = s * s := by rw [hs]; exact finite_adele_snd_algebraMap Δ v
  have A1 : a * a + ΔA * (b * b) = a := by
    apply hAF
    · simp only [finite_adele_fst_add, finite_adele_fst_mul, ha1, hb1]
      ring
    · intro w
      simp only [finite_adele_snd_add, finite_adele_snd_mul]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, hb2v, hDAv]
        field_simp
        ring
      · rw [ha2w w hw, hb2w w hw]
        ring
  have A2 : a * b + a * b = b := by
    apply hAF
    · simp only [finite_adele_fst_add, finite_adele_fst_mul, ha1, hb1]
      ring
    · intro w
      simp only [finite_adele_snd_add, finite_adele_snd_mul]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, hb2v]
        field_simp
        ring
      · rw [ha2w w hw, hb2w w hw]
        ring
  have A3 : a * a - ΔA * (b * b) = 0 := by
    apply hAF
    · simp only [finite_adele_fst_sub, finite_adele_fst_mul, ha1, hb1]
      rw [show (0 : AF D.host.F).1 = 0 from rfl]
      ring
    · intro w
      simp only [finite_adele_snd_sub, finite_adele_snd_mul]
      rw [show (0 : AF D.host.F).2 w = 0 from rfl]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, hb2v, hDAv]
        field_simp
        ring
      · rw [ha2w w hw, hb2w w hw]
        ring
  have A4 : a + a = epv v := by
    apply hAF
    · simp only [finite_adele_fst_add, ha1, epv_fst]
      ring
    · intro w
      simp only [finite_adele_snd_add]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, epv_self, ← two_mul, mul_inv_cancel₀ h2F]
      · rw [ha2w w hw, epv_ne hw]
        ring
  obtain ⟨ι, hι⟩ : ∃ f : AF D.host.F →+* AE D, f = algebraMap (AF D.host.F) (AE D) := ⟨_, rfl⟩
  have hιt : ∀ x : AF D.host.F, ι x = x ⊗ₜ[D.host.F] (1 : D.host.E) := by intro x; rw [hι]; rfl
  obtain ⟨d, hd⟩ : ∃ d : AE D, d = (1 : AF D.host.F) ⊗ₜ[D.host.F] δ := ⟨_, rfl⟩
  have kd : d * d = ι ΔA := by
    rw [hd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hΔ, hιt,
      show algebraMap D.host.F D.host.E Δ = Δ • (1 : D.host.E) from Algebra.algebraMap_eq_smul_one Δ,
      ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have k1 : ι a * ι a + ι ΔA * (ι b * ι b) = ι a := by
    simpa only [map_add (f := _), map_mul] using congrArg ι A1
  have k2 : ι a * ι b + ι a * ι b = ι b := by
    simpa only [map_add (f := _), map_mul] using congrArg ι A2
  have k3 : ι a * ι a - ι ΔA * (ι b * ι b) = 0 := by
    simpa only [map_sub, map_mul, map_zero] using congrArg ι A3
  have k4 : ι a + ι a = ι (epv v) := by
    simpa only [map_add (f := _)] using congrArg ι A4
  have hcι : ∀ x, cA D (ι x) = ι x := by
    intro x
    rw [hιt, hc, map_one]
  have hcd : cA D (ι b * d) = -(ι b * d) := by
    rw [hιt, hd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hc, hδ, TensorProduct.tmul_neg]
  have hce : cA D (ι a + ι b * d) = ι a - ι b * d := by
    rw [map_add (f := _), hcι, hcd, sub_eq_add_neg]
  have hsum : ι a + ι b * d + cA D (ι a + ι b * d) = algebraMap (AF D.host.F) (AE D) (epv v) := by
    rw [hce, ← hι, ← k4]
    ring
  refine ⟨ι a + ι b * d, ⟨?_, ?_, v, epv v, ?_, hsum⟩, hsum⟩
  · linear_combination k1 + d * k2 + ι b * ι b * kd
  · rw [hce]
    linear_combination k3 - ι b * ι b * kd
  · exact ⟨single v 1, rfl, epv_self v, fun v' hv' => epv_ne hv'⟩


end Split

end Formalism.IndefR.Fin.U1

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev latAll (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : AddSubgroup (WO S T) :=
  latO S T ΛS ΛT fun _ => True

def PlaceLatDual (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ e' : AE D, IsSplitIdem D e' → ∀ u ∈ latAll S T ΛS ΛT, u.map (fun a => e' * a) ∈ latAll S T ΛS ΛT) ∧
    (∀ e' : AE D, IsSplitIdem D e' → ∀ (g : GA D S) (h : GA D T), SuppAt e' S g → SuppAt e' T h →
      ∃ k : ℕ, 0 < k ∧ ∀ t ∈ latAll S T ΛS ΛT, k • actO S T g h t ∈ latAll S T ΛS ΛT) ∧
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ y : WO S T, IsHalf (cA D e) y →
        ((∀ x ∈ latAll S T ΛS ΛT, IsHalf e x → ψ (symplO S T x y) = 1) ↔ y ∈ latAll S T ΛS ΛT)) ∧
      (∀ x : WO S T, IsHalf e x →
        ((∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT)) ∧
      (∀ k : ℕ, 0 < k → ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
          ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v) ∧
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) → ∀ x : WO S T, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ latAll S T ΛS ΛT

def PlaceModelAt (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ →
      (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) →
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ (latAll S T ΛS ΛT) 1 f₀ Tm ∧
          (∀ Tm', IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ (latAll S T ΛS ΛT) 1 f₀ Tm' →
            ∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → Tm' Φ = Tm Φ) ∧
          (∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → IsThetaFunO ψ S T (Tm Φ)) ∧
          ∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → ∀ u : WO S T, (∀ i j, (e + cA D e) * u i j = 0) →
            heisO ψ S T u f₀ = f₀ → heisO ψ S T u (Tm Φ) = Tm Φ

def SplitLin (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) →
    ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm →
    ∀ e₁ : AE D, IsSplitIdem D e₁ → e₁ * e = e₁ →
    ∀ (g : GA D S) (h : GA D T), SuppAt e₁ S g → SuppAt e₁ T h →
    ∀ x y : (AE D)ˣ, IsDetAt e₁ S g x → IsDetAt e₁ T h y →
      ∃ r : ℝ, 0 < r ∧
        (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ →
          om (g, h) (Tm Φ) = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • Tm (fun t => Φ (actO S T g⁻¹ h⁻¹ t))) ∧
        ((∀ t : WO S T, IsHalf e t → (actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT)) →
          (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1) → r = 1)

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

def TwoSplits (D : D7) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), (2 : 𝓞 D.host.E) ∈ P.asIdeal → ¬ Lev.IsConjPl (D := D) P P

def TwoSplitIdem (D : D7) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal →
    ∃ (e : AE D) (ε : AF D.host.F), IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def LatSelfDual (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
      (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT →
      IsCompact ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True :
          AddSubgroup (WO S T)) : Set (WO S T)) ∧
      IsOpen {w : WO S T | ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
          (fun _ => True), (w - u).map (finPart D) = 0} ∧
      (∀ a : AE D, finPart D a ∈ intAE D →
        ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          a • u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ x : WO S T, x.map (infPart D) = 0 →
        (x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
          ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
            ψ (symplO S T x u) = 1)


def HeisStable (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (w₀ : WO S T) (f : WO S T → ℂ),
    IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w₀ f)

def DRhoStable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f)

def PtStable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ)
      (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P)

end Formalism.IndefR.Fin

end
end

