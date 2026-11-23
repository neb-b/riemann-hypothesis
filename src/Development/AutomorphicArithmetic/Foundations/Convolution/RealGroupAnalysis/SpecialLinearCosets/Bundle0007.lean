module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ContinuousQuaternaryFormLeft
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem continuous_form {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a c b d e : R) :
    Continuous fun y : Fin 4 → R => 2 * (y 2 * a - c * (y 3 * b)) - y 1 * d - y 0 * e := by
  fun_prop

private theorem continuous_psi {F : Type} [Field F] [NumberField F] : Continuous (ψ : A F → ℂ) :=
  continuous_subtype_val.comp (continuous_adelicChar (K := F))

private theorem norm_psi {F : Type} [Field F] [NumberField F] (x : A F) : ‖ψ x‖ = 1 :=
  Circle.norm_coe _

private theorem psi_add {F : Type} [Field F] [NumberField F] (x y : A F) :
    ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem continuous_quaternaryForm_left {F : Type} [Field F] [NumberField F] (δ : F) (Z : V4 F) :
    Continuous fun y : V4 F => B4 δ y Z :=
  continuous_form (Z 2) (rt δ) (Z 3) (Z 0) (Z 1)

private theorem continuous_BM {F : Type} [Field F] [NumberField F] (v : P F) (M : M2 v) :
    Continuous fun Y : M2 v => BM Y M := by
  unfold BM
  have h : ∀ i j, Continuous fun Y : M2 v => Y i j := fun i j => continuous_id.matrix_elem i j
  exact (((h 0 1).mul continuous_const).add ((h 1 0).mul continuous_const)).sub
    ((h 0 0).mul continuous_const) |>.sub ((h 1 1).mul continuous_const)

private theorem mul_mem_SB {F : Type} [Field F] [NumberField F] (v : P F) {b : M2 v → ℂ}
    (hb : b ∈ SB (M2 v)) (M : M2 v) (hψ : IsLocallyConstant (ψl v)) :
    (fun Y => b Y * ψl v (BM Y M)) ∈ SB (M2 v) :=
  ⟨hb.1.mul (hψ.comp_continuous (continuous_BM v M)), hb.2.mul_right⟩

theorem UpperTheory.ConvolutionTheory.R2.I.tenFt :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (v : P F) (δ : F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) δ → θ ≠ 0 →
      ∀ u, GoodU v δ θ u → ∃ u' : V4 F → ℂ, ∀ b ∈ SB (M2 v),
        ft4 δ (ten v θ u b) = ten v θ u' fun X => IM fun Y => b Y * ψl v (BM Y X) := by
  intro F _ _ _ v δ θ hθ hθ0 u hu
  obtain ⟨hm1, hm2, -, -, hac, -, -⟩ := matLaws F v δ θ hθ hθ0
  obtain ⟨-, hψs, -, hψlc, -, -⟩ := psiLaws F v
  have hint : ∀ b ∈ SB (M2 v), ∀ Z : V4 F,
      Integrable (fun Y => ten v θ u b Y * ψ (B4 δ (away v Y) Z)) (adeleMeasurePi F) := by
    intro b hb Z
    obtain ⟨φ, -, hφ⟩ := hu b hb
    rw [← hφ]
    refine (integrable_of_mem_schwartzBruhatPi φ.2).mul_bdd (c := 1) ?_ ?_
    · exact (continuous_psi.comp ((continuous_quaternaryForm_left δ Z).comp hac)).aestronglyMeasurable
    · exact Eventually.of_forall fun y => (norm_psi _).le
  let ℓ : V4 F → SB (M2 v) →ₗ[ℂ] ℂ := fun Z =>
    { toFun := fun b => ∫ Y, ten v θ u b.1 Y * ψ (B4 δ (away v Y) Z) ∂(adeleMeasurePi F)
      map_add' := by
        intro a b
        rw [← integral_add (hint a.1 a.2 Z) (hint b.1 b.2 Z)]
        congr 1
        funext Y
        simp only [ten, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1
        funext Y
        simp only [ten, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring }
  have hinv : ∀ (Z : V4 F) (y : M2 v) (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m + y)) →
      ℓ Z a' = ℓ Z a := by
    intro Z y a a' h
    obtain ⟨y', hy'⟩ := hm1 y
    change (∫ Y, ten v θ u a'.1 Y * ψ (B4 δ (away v Y) Z) ∂(adeleMeasurePi F)) =
      ∫ Y, ten v θ u a.1 Y * ψ (B4 δ (away v Y) Z) ∂(adeleMeasurePi F)
    rw [← integral_add_right_eq_self
      (fun Y => ten v θ u a.1 Y * ψ (B4 δ (away v Y) Z)) y']
    congr 1
    funext Y
    simp only [ten, (hy' Y).1, (hy' Y).2, h]
  choose c hc using fun Z => invFn F v (ℓ Z) (hinv Z)
  refine ⟨c, fun b hb => ?_⟩
  funext X
  have hmem := mul_mem_SB v hb (mat v θ X) hψlc
  have h := hc (away v X) ⟨_, hmem⟩
  change (∫ Y, ten v θ u (fun Y => b Y * ψl v (BM Y (mat v θ X))) Y *
    ψ (B4 δ (away v Y) (away v X)) ∂(adeleMeasurePi F)) = _ at h
  simp only [ten]
  rw [← h]
  unfold ft4
  congr 1
  funext Y
  rw [hm2 X Y, psi_add, hψs]
  simp only [ten]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.DetMulInv
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] {v : P F}

private lemma det_inv_mul (y : GLv v) : ((y⁻¹).val).det * (y.val).det = 1 := by
  rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]

private lemma det_mul_inv (y : GLv v) : (y.val).det * ((y⁻¹).val).det = 1 := by
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

private noncomputable def tw (y h : GLv v) (e : (y.val).det = (h.val).det) : SL v ≃ₜ SL v where
  toFun m := ⟨(y⁻¹).val * m.1 * h.val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, ← e, det_inv_mul]⟩
  invFun m := ⟨y.val * m.1 * (h⁻¹).val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, e, det_mul_inv]⟩
  left_inv m := by
    apply Subtype.ext
    have hy : y.val * (y⁻¹).val = 1 := Units.mul_inv y
    have hh : h.val * (h⁻¹).val = 1 := Units.mul_inv h
    change y.val * ((y⁻¹).val * m.1 * h.val) * (h⁻¹).val = m.1
    calc y.val * ((y⁻¹).val * m.1 * h.val) * (h⁻¹).val
        = (y.val * (y⁻¹).val) * m.1 * (h.val * (h⁻¹).val) := by simp only [Matrix.mul_assoc]
      _ = m.1 := by rw [hy, hh, Matrix.one_mul, Matrix.mul_one]
  right_inv m := by
    apply Subtype.ext
    have hy : (y⁻¹).val * y.val = 1 := Units.inv_mul y
    have hh : (h⁻¹).val * h.val = 1 := Units.inv_mul h
    change (y⁻¹).val * (y.val * m.1 * (h⁻¹).val) * h.val = m.1
    calc (y⁻¹).val * (y.val * m.1 * (h⁻¹).val) * h.val
        = ((y⁻¹).val * y.val) * m.1 * ((h⁻¹).val * h.val) := by simp only [Matrix.mul_assoc]
      _ = m.1 := by rw [hy, hh, Matrix.one_mul, Matrix.mul_one]
  continuous_toFun := by
    refine Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
    exact (continuous_const.matrix_mul Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_mul continuous_const
  continuous_invFun := by
    refine Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
    exact (continuous_const.matrix_mul Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_mul continuous_const

private noncomputable def cj (w : GLv v) : SL v →* SL v where
  toFun := tw w w rfl
  map_one' := by
    apply Subtype.ext
    have hw : (w⁻¹).val * w.val = 1 := Units.inv_mul w
    change (w⁻¹).val * (1 : M2 v) * w.val = 1
    rw [Matrix.mul_one, hw]
  map_mul' m n := by
    apply Subtype.ext
    have hw : w.val * (w⁻¹).val = 1 := Units.mul_inv w
    change (w⁻¹).val * (m.1 * n.1) * w.val = ((w⁻¹).val * m.1 * w.val) * ((w⁻¹).val * n.1 * w.val)
    calc (w⁻¹).val * (m.1 * n.1) * w.val
        = (w⁻¹).val * m.1 * (1 : M2 v) * n.1 * w.val := by
          rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = ((w⁻¹).val * m.1 * w.val) * ((w⁻¹).val * n.1 * w.val) := by
          rw [← hw]; simp only [Matrix.mul_assoc]

private lemma sb_comp {X : Type} [TopologicalSpace X] (e : X ≃ₜ X) {b : X → ℂ} (hb : b ∈ SB X) :
    b ∘ e ∈ SB X :=
  ⟨hb.1.comp_continuous e.continuous, hb.2.comp_homeomorph e⟩

private lemma ind_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {U : Subgroup G} (hUo : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) : ind U ∈ SB G := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
    HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (U : Set G)
  · exact ⟨U, hUo, hx, fun y hy => by
      simp only [ind]; rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(U : Set G)ᶜ, (U.isClosed_of_isOpen hUo).isOpen_compl, hx, fun y hy => by
      simp only [ind]; rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private lemma one_term {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V)
    (β : V →ₗ[ℂ] SB (SL v) →ₗ[ℂ] ℂ)
    (hβ : ∀ (g : SL v) f (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) →
      β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a)
    (I : SB (SL v) →ₗ[ℂ] ℂ) (hI : InvI I) (Λ : V →ₗ[ℂ] ℂ)
    (hΛ : ∀ f (U : Subgroup (SL v)) (a : SB (SL v)), IsOpen (U : Set (SL v)) → a.1 = ind U →
      (∀ g ∈ U, ρ (Matrix.SpecialLinearGroup.toGL g) f = f) → β f a = I a * Λ f)
    (U : Subgroup (SL v)) (hUo : IsOpen (U : Set (SL v))) (a0 : SB (SL v)) (ha0 : a0.1 = ind U)
    (f : V) (hfix : ∀ u ∈ U, ρ (Matrix.SpecialLinearGroup.toGL u) f = f)
    (w d : GLv v) (e : (w.val).det = (d.val).det) (b : SB (SL v))
    (hb : ∀ m, b.1 m = ind U (tw w d e m)) :
    β (ρ d f) b = I a0 * Λ (ρ w f) := by
  have hdi : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  have hwi : w.val * (w⁻¹).val = 1 := Units.mul_inv w
  let g' : SL v := ⟨w.val * (d⁻¹).val, by rw [Matrix.det_mul, e, det_mul_inv]⟩
  have hg' : Matrix.SpecialLinearGroup.toGL g' * d = w := by
    apply Units.ext
    change w.val * (d⁻¹).val * d.val = w.val
    rw [Matrix.mul_assoc, hdi, Matrix.mul_one]
  let Uc : Subgroup (SL v) := U.comap (cj w)
  have hUco : IsOpen (Uc : Set (SL v)) := hUo.preimage (tw w w rfl).continuous
  have hU0 : ind U ∈ SB (SL v) := ha0 ▸ a0.2
  let a1 : SB (SL v) := ⟨ind U ∘ (tw w w rfl), sb_comp _ hU0⟩
  have h1 : a1.1 = ind Uc := by
    funext m
    change ind U (tw w w rfl m) = ind Uc m
    unfold ind
    by_cases h : tw w w rfl m ∈ U
    · rw [Set.indicator_of_mem (show _ ∈ (U : Set (SL v)) from h),
        Set.indicator_of_mem (show m ∈ (Uc : Set (SL v)) from h)]
    · rw [Set.indicator_of_notMem (show _ ∉ (U : Set (SL v)) from h),
        Set.indicator_of_notMem (show m ∉ (Uc : Set (SL v)) from h)]
  have h2 : β (ρ (Matrix.SpecialLinearGroup.toGL g') (ρ d f)) a1 = β (ρ d f) b :=
    hβ g' (ρ d f) b a1 fun m => by
      rw [hb]
      change ind U (tw w w rfl m) = ind U (tw w d e (m * g'))
      congr 1
      apply Subtype.ext
      change (w⁻¹).val * m.1 * w.val = (w⁻¹).val * (m.1 * (w.val * (d⁻¹).val)) * d.val
      simp only [Matrix.mul_assoc]
      rw [hdi, Matrix.mul_one]
  have h3 : ρ (Matrix.SpecialLinearGroup.toGL g') (ρ d f) = ρ w f := by
    rw [← Module.End.mul_apply, ← map_mul, hg']
  have h4 : ∀ u ∈ Uc, ρ (Matrix.SpecialLinearGroup.toGL u) (ρ w f) = ρ w f := by
    intro u hu
    have hw : Matrix.SpecialLinearGroup.toGL u * w = w * Matrix.SpecialLinearGroup.toGL (tw w w rfl u) := by
      apply Units.ext
      change u.1 * w.val = w.val * ((w⁻¹).val * u.1 * w.val)
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hwi, Matrix.one_mul]
    have h5 : ρ (Matrix.SpecialLinearGroup.toGL (tw w w rfl u)) f = f := hfix _ hu
    calc ρ (Matrix.SpecialLinearGroup.toGL u) (ρ w f)
        = ρ (Matrix.SpecialLinearGroup.toGL u * w) f := by rw [map_mul, Module.End.mul_apply]
      _ = ρ w (ρ (Matrix.SpecialLinearGroup.toGL (tw w w rfl u)) f) := by
          rw [hw, map_mul, Module.End.mul_apply]
      _ = ρ w f := by rw [h5]
  have h6 : I a1 = I a0 := hI.conj w a0 a1 fun m m' h => by
    have : m' = tw w w rfl m := Subtype.ext h
    rw [this, ha0]
    rfl
  rw [← h2, h3, hΛ (ρ w f) Uc a1 hUco h1 h4, h6]

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.absS :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V), (∀ f, IsOpen {g | ρ g f = f}) →
      ∀ β : V →ₗ[ℂ] SB (SL v) →ₗ[ℂ] ℂ,
      (∀ (g : SL v) f (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) → β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a) →
      ∀ f (a : SB (SL v)) (aa : GLv v → SB (SL v)),
        (∀ x (m m' : SL v), m'.1 = (x⁻¹).val * m.1 * (dd x).val → (aa x).1 m = a.1 m') → (fun x => β (ρ (dd x) f) (aa x)) ∈ MC ρ := by
  intro F _ _ v V _ _ ρ hsm β hβ f a aa haa
  obtain ⟨I, hI⟩ := UpperTheory.ConvolutionTheory.R2.I.invI F v
  obtain ⟨Λ, hΛ⟩ := UpperTheory.ConvolutionTheory.R2.I.lamEx F v V ρ hsm I hI β hβ
  have hN : (Matrix.SpecialLinearGroup.toGL : SL v → GLv v) ⁻¹' {g | ρ g f = f} ∈ 𝓝 (1 : SL v) :=
    ((hsm f).preimage Matrix.SpecialLinearGroup.continuous_toGL).mem_nhds (by simp)
  obtain ⟨U, s, c, hUo, hUc, hUN, hsum⟩ :=
    UpperTheory.ConvolutionTheory.R2.I.cosetSpan (SL v) (UpperTheory.ConvolutionTheory.R2.I.lgrp F v).1 a.1 a.2 _ hN
  let a0 : SB (SL v) := ⟨ind U, ind_mem hUo hUc⟩
  have hfix : ∀ u ∈ U, ρ (Matrix.SpecialLinearGroup.toGL u) f = f := fun u hu => hUN hu
  have hdet0 : ∀ x : GLv v, (x.val).det = ((dd x).val).det := by
    intro x
    change _ = (!![(((1 : (Kv v)ˣ)) : Kv v), 0; 0, ((Matrix.GeneralLinearGroup.det x : (Kv v)ˣ) : Kv v)]).det
    simp [Matrix.det_fin_two_of]
  have hdet : ∀ (x : GLv v) (g : SL v),
      ((x * Matrix.SpecialLinearGroup.toGL g).val).det = ((dd x).val).det := by
    intro x g
    rw [← hdet0 x, Units.val_mul, Matrix.det_mul]
    have : ((Matrix.SpecialLinearGroup.toGL g).val).det = 1 := g.2
    rw [this, mul_one]
  have hval : ∀ x, β (ρ (dd x) f) (aa x) =
      ∑ g ∈ s, (c g * I a0) * Λ (ρ x (ρ (Matrix.SpecialLinearGroup.toGL g) f)) := by
    intro x
    let B : SL v → SB (SL v) := fun g =>
      ⟨ind U ∘ tw (x * Matrix.SpecialLinearGroup.toGL g) (dd x) (hdet x g), sb_comp _ a0.2⟩
    have hs : aa x = ∑ g ∈ s, c g • B g := by
      apply Subtype.ext
      funext m
      rw [haa x m (tw x (dd x) (hdet0 x) m) rfl, hsum]
      simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      change ind U _ = ind U (tw (x * Matrix.SpecialLinearGroup.toGL g) (dd x) (hdet x g) m)
      congr 1
      apply Subtype.ext
      have hinv : ((x * Matrix.SpecialLinearGroup.toGL g)⁻¹).val = (g⁻¹).1 * (x⁻¹).val := by
        rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul]
        rfl
      change (g⁻¹).1 * ((x⁻¹).val * m.1 * (dd x).val) =
        ((x * Matrix.SpecialLinearGroup.toGL g)⁻¹).val * m.1 * (dd x).val
      rw [hinv]
      simp only [Matrix.mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, smul_eq_mul,
      one_term ρ β hβ I hI Λ hΛ U hUo a0 rfl f hfix (x * Matrix.SpecialLinearGroup.toGL g) (dd x)
        (hdet x g) (B g) (fun m => rfl), map_mul, Module.End.mul_apply, mul_assoc]
  have hfun : (fun x => β (ρ (dd x) f) (aa x)) =
      ∑ g ∈ s, (c g * I a0) • (fun x => Λ (ρ x (ρ (Matrix.SpecialLinearGroup.toGL g) f))) := by
    funext x
    rw [hval x]
    simp [Finset.sum_apply]
  rw [hfun]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Λ, _, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IntegrableCols
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I.ColumnIntegrability

variable {F : Type} [Field F] [NumberField F] {v : P F}

private def colsH : ((Fin 2 → Kv v) × (Fin 2 → Kv v)) ≃ₜ M2 v where
  toFun p := cols p.1 p.2
  invFun m := (fun i => m i 0, fun i => m i 1)
  left_inv p := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp [cols]
  right_inv m := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [cols]
  continuous_toFun := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [cols] <;> simp <;> fun_prop
  continuous_invFun :=
    (continuous_pi fun i => continuous_id.matrix_elem i 0).prodMk
      (continuous_pi fun i => continuous_id.matrix_elem i 1)

private theorem integrable_cols {b : M2 v → ℂ} (hb : b ∈ SB (M2 v)) {g : (Fin 2 → Kv v) × (Fin 2 → Kv v) → ℂ}
    (hg : Continuous g) :
    Integrable (fun p => b (cols p.1 p.2) * g p) ((μ2 v).prod (μ2 v)) := by
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  have hc : Continuous fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => b (cols p.1 p.2) :=
    hb.1.continuous.comp (colsH (v := v)).continuous
  have hs : HasCompactSupport fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => b (cols p.1 p.2) :=
    hb.2.comp_homeomorph (colsH (v := v))
  exact (hc.mul hg).integrable_of_hasCompactSupport hs.mul_right

end UpperTheory.ConvolutionTheory.R2.I.ColumnIntegrability

namespace UpperTheory.ConvolutionTheory.R2.I.ColumnIntegrability

variable {F : Type} [Field F] [NumberField F] {v : P F}

private theorem inv_col {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) (e c : Fin 2 → Kv v) :
    ∫ e₁, Pt a (cols e₁ e) * ψl v (c 0 * e₁ 1 - c 1 * e₁ 0) ∂(μ2 v) = a (cols e c) := by
  have h := (UpperTheory.ConvolutionTheory.R2.I.ptInv F v a ha).1 (cols e c)
  refine Eq.trans ?_ h
  have hP : ∀ (g : M2 v → ℂ) (Y : M2 v), Pt g Y =
      ∫ c', g (cols (fun i => Y i 1) c') * ψl v (Y 0 0 * c' 1 - Y 1 0 * c' 0) ∂(μ2 v) := fun _ _ => rfl
  rw [hP (fun X => Pt a (sw X))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have h1 : (fun i => sw (cols e c) i 1) = e := by
    funext i; fin_cases i <;> simp [sw, cols]
  have h2 : ∀ y : Fin 2 → Kv v, sw (cols e y) = cols y e := by
    intro y; ext i j; fin_cases i <;> fin_cases j <;> simp [sw, cols]
  have h3 : sw (cols e c) 0 0 = c 0 := by simp [sw, cols]
  have h4 : sw (cols e c) 1 0 = c 1 := by simp [sw, cols]
  simp only [h1, h3, h4]
  rw [h2]

private theorem cont_lin {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (s t u w : R) :
    Continuous fun p : (Fin 2 → R) × (Fin 2 → R) => (s * p.2 0 - t * p.2 1) + (u * p.1 1 - w * p.1 0) := by
  fun_prop

private theorem bm_cols (X : M2 v) (x e : Fin 2 → Kv v) :
    BM (cols x e) X = (X 1 0 * e 0 - X 0 0 * e 1) + (X 0 1 * x 1 - X 1 1 * x 0) := by
  simp [BM, cols]; ring

private theorem cols_mul_w (c c' : Fin 2 → Kv v) :
    cols c c' * !![0, 1; -1, 0] = cols (-c') c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cols, Matrix.mul_apply, Fin.sum_univ_two]

end UpperTheory.ConvolutionTheory.R2.I.ColumnIntegrability

open UpperTheory.ConvolutionTheory.R2.I.ColumnIntegrability in
theorem UpperTheory.ConvolutionTheory.R2.I.ptW :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∀ a ∈ SB (M2 v), ∀ X, IM (fun Y => Pt a Y * ψl v (BM Y X)) = Pt (fun m => a (m * !![0, 1; -1, 0])) X := by
  intro F _ _ v a ha X
  obtain ⟨T, hT⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have hb : Pt a ∈ SB (M2 v) := by
    have := (T ⟨a, ha⟩).2
    rwa [hT ⟨a, ha⟩] at this
  obtain ⟨-, -, hadd, hlc, -, -⟩ := UpperTheory.ConvolutionTheory.R2.I.psiLaws F v
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  have hcont : Continuous fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => ψl v (BM (cols p.1 p.2) X) := by
    simp only [bm_cols]
    exact hlc.continuous.comp (cont_lin _ _ _ _)
  have hint := integrable_cols hb hcont
  unfold IM
  rw [integral_prod_symm _ hint]
  set c : Fin 2 → Kv v := fun i => X i 1 with hc
  have hin : ∀ e : Fin 2 → Kv v,
      ∫ e₁, Pt a (cols e₁ e) * ψl v (BM (cols e₁ e) X) ∂(μ2 v) =
        ψl v (X 1 0 * e 0 - X 0 0 * e 1) * a (cols e c) := by
    intro e
    rw [← inv_col ha e c, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    have hc0 : c 0 = X 0 1 := rfl
    have hc1 : c 1 = X 1 1 := rfl
    rw [bm_cols, hadd, hc0, hc1]
    ring
  simp only [hin]
  rw [← integral_neg_eq_self]
  simp only [Pt]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [cols_mul_w]
  have : X 1 0 * (-x) 0 - X 0 0 * (-x) 1 = X 0 0 * x 1 - X 1 0 * x 0 := by
    simp; ring
  rw [this]
  exact mul_comm _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Splt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.splt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (w : P E) (i : Kv v ≃+* Kv w), Continuous i →
      (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
      ∃ θ : Kv v, Splt D v θ ((lc w).comp (Matrix.GeneralLinearGroup.map i.toRingHom)) := by
  intro F E _ _ _ _ _ D v w i hc hal
  obtain ⟨θ, hsq, hne, hk⟩ := UpperTheory.ConvolutionTheory.R2.I.place F E D v w i hc hal
  obtain ⟨-, -, -, -, hlc, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws E w
  have hone : ∀ a b : Fin 2, i ((1 : Matrix (Fin 2) (Fin 2) (Kv v)) a b) =
      (1 : Matrix (Fin 2) (Fin 2) (Kv w)) a b := by
    intro a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨θ, hsq, hne, ?_, ?_⟩
  · intro x a b
    have e : (Matrix.GeneralLinearGroup.map i.toRingHom x).val a b = i (x.val a b) := rfl
    change (lc w (Matrix.GeneralLinearGroup.map i.toRingHom x)).val a b = _
    rw [hlc, e, ← hone, ← map_sub, hk]
  · intro x
    exact ⟨locGL E 2 w (Matrix.GeneralLinearGroup.map i.toRingHom x), rfl⟩
end

