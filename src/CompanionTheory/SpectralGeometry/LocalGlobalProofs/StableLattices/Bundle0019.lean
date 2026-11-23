module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.Bundle0004

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsUnitOfTmulOne
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.QTie

theorem isUnit_of_tmul_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {R : Type} [CommRing R] [Algebra F R] {c : R}
    (h : IsUnit (c ⊗ₜ[F] (1 : E))) : IsUnit c := by
  obtain ⟨bb, -, -⟩ := GlobalTheory.CompanionTheory.SW.OneHerm.exists_basis hσ
  have h1 := h.map (Algebra.norm R (S := R ⊗[F] E))
  have h2 := Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis R bb) c
  rw [Algebra.TensorProduct.algebraMap_apply] at h2
  have h3 : Algebra.norm R (c ⊗ₜ[F] (1 : E)) = c ^ 2 := by simpa using h2
  rw [h3] at h1
  exact (isUnit_pow_iff two_ne_zero).mp h1

def hermAdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : R ≃+ HermR R σ 1 where
  toFun := hermScal R σ
  invFun := GlobalTheory.CompanionTheory.SW.OneHerm.hermHalf R σ
  left_inv := GlobalTheory.CompanionTheory.SW.OneHerm.hermHalf_hermScal R hσ
  right_inv := GlobalTheory.CompanionTheory.SW.OneHerm.hermScal_hermHalf R hσ
  map_add' a b := by
    apply Subtype.ext
    ext i j
    change (a + b) ⊗ₜ[F] (1 : E) = a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] (1 : E)
    rw [TensorProduct.add_tmul]

end GlobalTheory.CompanionTheory.SW.QTie


open GlobalTheory.CompanionTheory.SW.OneHerm GlobalTheory.CompanionTheory.SW.QTie in
theorem GlobalTheory.CompanionTheory.SW.QTie.fib_eq_gramFib : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 → μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) X)} = 0 → ∀ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) id Set.univ ν {c | IsUnit c} fib → ∀ m, IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m → ∀ c : R, IsUnit c → fib c = m (hermScal R σ c) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR μ ν hμ hν hνu hμu fib hfib m hm c hc
  classical
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor 1 M
  obtain ⟨hL, hS2, hT, hB, hg⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R 1
  haveI := hL
  haveI := hS2
  haveI := hT
  haveI := hB
  obtain ⟨g, hgc, hgf⟩ := hg M J hJ
  obtain ⟨hf1, hf2, hf3⟩ := hfib
  let q : (Fin 1 → Fin M → R ⊗[F] E) → R := fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0)
  have hq : ∀ X, q X = OneHerm.hermHalf R σ (g X) := by
    intro X
    change _ = algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((g X : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)
    rw [← hgf X]
    rfl
  have hgq : ∀ X, g X = hermScal R σ (q X) := by
    intro X
    rw [hq, OneHerm.hermScal_hermHalf R hσ]
  have hdet : ∀ S : HermR R σ 1, IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det ↔ IsUnit (OneHerm.hermHalf R σ S) := by
    intro S
    have hS : ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det = (OneHerm.hermHalf R σ S) ⊗ₜ[F] (1 : E) := by
      conv_lhs => rw [← OneHerm.hermScal_hermHalf R hσ S]
      rw [Matrix.det_fin_one]
      rfl
    rw [hS]
    refine ⟨QTie.isUnit_of_tmul_one hσ, fun h => ?_⟩
    exact h.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)
  have hU : {X | IsUnit (gramR R σ J X).det} = {X | IsUnit (q X)} := by
    ext X
    simp only [Set.mem_setOf_eq]
    rw [hgf X, hdet, hq]
  have hUnull : μ ({X | IsUnit (gramR R σ J X).det}ᶜ) = 0 := by
    rw [hU]
    exact hμu
  have hemb : MeasurableEmbedding (hermScal R σ) := (OneHerm.hermHomeo R hσ).measurableEmbedding
  have hν' : (ν.map (hermScal R σ)).IsAddHaarMeasure :=
    (QTie.hermAdd hσ R).isAddHaarMeasure_map ν (OneHerm.continuous_hermScal R σ) (OneHerm.continuous_hermHalf R σ)
  let m' : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E) := fun S =>
    if IsUnit (OneHerm.hermHalf R σ S) then fib (OneHerm.hermHalf R σ S) else 0
  have hm'u : ∀ s : R, IsUnit s → m' (hermScal R σ s) = fib s := by
    intro s hs
    simp only [m', OneHerm.hermHalf_hermScal R hσ, hs, if_true]
  have hm' : IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m' := by
    refine ⟨?_, ?_, ?_⟩
    · intro S
      by_cases hS : IsUnit (OneHerm.hermHalf R σ S)
      · have : m' S = fib (OneHerm.hermHalf R σ S) := by simp only [m', hS, if_true]
        rw [this]
        refine measure_mono_null ?_ (hf1 (OneHerm.hermHalf R σ S))
        intro X hX hX'
        apply hX
        have hqX : q X = OneHerm.hermHalf R σ S := by simpa using hX'.1
        refine ⟨?_, ?_⟩
        · change gramR R σ J X = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))
          rw [hgf X, hgq X, hqX, OneHerm.hermScal_hermHalf R hσ]
        · change IsUnit (gramR R σ J X).det
          rw [hgf X, hdet, ← hq, hqX]
          exact hS
      · have : m' S = 0 := by simp only [m', hS, if_false]
        rw [this]
        rfl
    · intro φ hφ
      rw [hemb.lintegral_map]
      have h1 : ∫⁻ v in {X | IsUnit (gramR R σ J X).det}, φ v ∂μ = ∫⁻ v in Set.univ, φ v ∂μ := by
        rw [Measure.restrict_univ]
        rw [Measure.restrict_eq_self_of_ae_mem]
        exact measure_eq_zero_iff_ae_notMem.mp hUnull |>.mono fun x hx => by simpa using hx
      rw [h1, hf2 φ hφ]
      refine lintegral_congr_ae ?_
      have hae : ∀ᵐ s ∂ν, IsUnit s := by
        rw [ae_iff]
        exact hνu
      filter_upwards [hae] with s hs
      rw [hm'u s hs]
    · intro φ hφ hφc hφs
      obtain ⟨hi, hcont⟩ := hf3 φ hφ hφc (Set.subset_univ _)
      refine ⟨fun S hS => ?_, ?_⟩
      · have hS' : IsUnit (OneHerm.hermHalf R σ S) := (hdet S).mp hS
        have : m' S = fib (OneHerm.hermHalf R σ S) := by simp only [m', hS', if_true]
        rw [this]
        exact hi _ hS'
      · have hmaps : Set.MapsTo (OneHerm.hermHalf R σ) {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} {c | IsUnit c} :=
          fun S hS => (hdet S).mp hS
        refine (hcont.comp (OneHerm.continuous_hermHalf R σ).continuousOn hmaps).congr ?_
        intro S hS
        have hS' : IsUnit (OneHerm.hermHalf R σ S) := (hdet S).mp hS
        have : m' S = fib (OneHerm.hermHalf R σ S) := by simp only [m', hS', if_true]
        simp only [this, Function.comp]
  have := GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique F E σ hσ M J hJ R hR 1 μ (ν.map (hermScal R σ)) m hμ hν' hm m' hm'
    (hermScal R σ c)
  rw [this, hm'u c hc]
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KummerLiftedCocycleImageEqPicardClass
section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSVerma

open CompanionTheory.D.DSIC Formalism.REAL

variable {n : ℕ} {ε : Fin n → Bool}

theorem sum_nc {R : Type} [AddCommMonoid R] (d b : Fin n) (g : Fin n → Fin n → R) :
    (∑ j : NC ε, if d = j.1.1 ∧ b = j.1.2 then g j.1.1 j.1.2 else 0) =
      if ε d = true ∧ ε b = false then g d b else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(d, b), h⟩ : NC ε)]
    · simp
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hj (Subtype.ext (Prod.ext h1.symm h2.symm))
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (by rw [h1, h2]; exact j.2)

section Abstract

variable {R : Type} [Ring R] (Y : NC ε → R) (u v : Fin n → Fin n → R)

theorem inner_sum
    (huY : ∀ a c j, u a c * Y j - Y j * u a c = -(if a = j.1.1 ∧ c = j.1.2 then 1 else 0))
    (hvY : ∀ a c j, v a c * Y j - Y j * v a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0)
    (i : NC ε) (c d e f : Fin n) :
    (∑ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2)) =
      u i.1.1 c * (if ε d = true then u d e else 0) * v f i.1.2 -
        v d i.1.2 * u i.1.1 e * (if ε c = false then v f c else 0) := by
  have h1 : ∀ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2) =
      (if d = j.1.1 ∧ i.1.2 = j.1.2 then u i.1.1 c * u j.1.1 e * v f j.1.2 else 0) -
        (if i.1.1 = j.1.1 ∧ c = j.1.2 then v d i.1.2 * u j.1.1 e * v f j.1.2 else 0) := by
    intro j
    have : (u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2) =
        u i.1.1 c * (v d i.1.2 * Y j - Y j * v d i.1.2) + (u i.1.1 c * Y j - Y j * u i.1.1 c) * v d i.1.2 := by
      noncomm_ring
    rw [this, huY, hvY]
    split_ifs <;> noncomm_ring
  simp only [h1, Finset.sum_sub_distrib]
  rw [sum_nc d i.1.2 (fun a b => u i.1.1 c * u a e * v f b),
    sum_nc i.1.1 c (fun a b => v d i.1.2 * u a e * v f b)]
  simp only [i.2.1, i.2.2, and_true, true_and]
  split_ifs <;> simp

theorem glRel_abstract (hYY : ∀ i j, Commute (Y i) (Y j))
    (huu : ∀ a b c d, Commute (u a b) (u c d)) (huv : ∀ a b c d, Commute (u a b) (v c d))
    (hvv : ∀ a b c d, Commute (v a b) (v c d))
    (huY : ∀ a c j, u a c * Y j - Y j * u a c = -(if a = j.1.1 ∧ c = j.1.2 then 1 else 0))
    (hvY : ∀ a c j, v a c * Y j - Y j * v a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0)
    (hs : ∀ d e, (if ε d = true then u d e else 0) + (if ε e = false then v d e else 0) =
      if d = e then 1 else 0) (c d e f : Fin n) :
    (∑ i : NC ε, Y i * (u i.1.1 c * v d i.1.2)) * (∑ i : NC ε, Y i * (u i.1.1 e * v f i.1.2)) -
      (∑ i : NC ε, Y i * (u i.1.1 e * v f i.1.2)) * (∑ i : NC ε, Y i * (u i.1.1 c * v d i.1.2)) =
      (if d = e then ∑ i : NC ε, Y i * (u i.1.1 c * v f i.1.2) else 0) -
        (if f = c then ∑ i : NC ε, Y i * (u i.1.1 e * v d i.1.2) else 0) := by
  have hprod : ∀ p q : NC ε → R, (∑ i, Y i * p i) * (∑ j, Y j * q j) =
      ∑ i, ∑ j, Y i * Y j * (p i * q j) + ∑ i, Y i * ∑ j, (p i * Y j - Y j * p i) * q j := by
    intro p q
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    noncomm_ring
  rw [hprod, hprod]
  have hsym : (∑ i : NC ε, ∑ j : NC ε, Y i * Y j * (u i.1.1 c * v d i.1.2 * (u j.1.1 e * v f j.1.2))) =
      ∑ i : NC ε, ∑ j : NC ε, Y i * Y j * (u i.1.1 e * v f i.1.2 * (u j.1.1 c * v d j.1.2)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(hYY j i).eq, (((huu _ _ _ _).mul_right (huv _ _ _ _)).mul_left
      ((huv _ _ _ _).symm.mul_right (hvv _ _ _ _))).eq]
  rw [hsym, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  have key : ∀ i : NC ε,
      Y i * (∑ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2)) -
      Y i * (∑ j : NC ε, ((u i.1.1 e * v f i.1.2) * Y j - Y j * (u i.1.1 e * v f i.1.2)) * (u j.1.1 c * v d j.1.2)) =
      (if d = e then Y i * (u i.1.1 c * v f i.1.2) else 0) -
        (if f = c then Y i * (u i.1.1 e * v d i.1.2) else 0) := by
    intro i
    rw [inner_sum Y u v huY hvY, inner_sum Y u v huY hvY]
    have e1 : ∀ c d e f : Fin n, v d i.1.2 * u i.1.1 e * (if ε c = false then v f c else 0) =
        u i.1.1 e * (if ε c = false then v f c else 0) * v d i.1.2 := by
      intro c d e f
      split_ifs
      · rw [mul_assoc]
        exact ((huv _ _ _ _).symm.mul_right (hvv _ _ _ _)).eq
      · simp
    rw [e1, e1]
    have h1 := hs d e
    have h2 := hs f c
    generalize (if ε d = true then u d e else 0) = A at *
    generalize (if ε e = false then v d e else 0) = B at *
    generalize (if ε f = true then u f c else 0) = C at *
    generalize (if ε c = false then v f c else 0) = D at *
    calc _ = Y i * (u i.1.1 c * (A + B) * v f i.1.2) - Y i * (u i.1.1 e * (C + D) * v d i.1.2) := by noncomm_ring
      _ = _ := by rw [h1, h2]; split_ifs <;> simp
  simp only [key, Finset.sum_sub_distrib]
  split_ifs <;> simp

end Abstract

open MvPolynomial

def dd (ε : Fin n → Bool) (a b : Fin n) : Module.End ℂ (MvPolynomial (NC ε) ℂ) :=
  if h : ε a = true ∧ ε b = false then (pderiv (⟨(a, b), h⟩ : NC ε)).toLinearMap else 0

def yy (i : NC ε) : Module.End ℂ (MvPolynomial (NC ε) ℂ) := LinearMap.mulLeft ℂ (X i)

theorem pderiv_comm' {σ : Type} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, hp, pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem dd_comm (a b c d : Fin n) : Commute (dd ε a b) (dd ε c d) := by
  unfold dd
  split_ifs
  · refine LinearMap.ext fun f => ?_
    exact pderiv_comm' _ _ f
  all_goals simp

theorem dd_yy (a c : Fin n) (j : NC ε) :
    dd ε a c * yy j - yy j * dd ε a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0 := by
  classical
  unfold dd yy
  split_ifs with h1 h2 h2
  · refine LinearMap.ext fun f => ?_
    have : j = ⟨(a, c), h1⟩ := Subtype.ext (Prod.ext h2.1.symm h2.2.symm)
    subst this
    simp
  · refine LinearMap.ext fun f => ?_
    have : j ≠ ⟨(a, c), h1⟩ := by
      rintro rfl
      exact h2 ⟨rfl, rfl⟩
    simp [pderiv_X_of_ne this]
  · exact absurd (by rw [h2.1, h2.2]; exact j.2) h1
  · simp

theorem verma : CompanionTheory.D.DSIC.Verma := by
  intro n ε
  let u : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ) := fun a c => (if a = c then 1 else 0) - dd ε a c
  let v : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ) := fun a c => (if a = c then 1 else 0) + dd ε a c
  have hδ : ∀ (a c : Fin n) (T : Module.End ℂ (MvPolynomial (NC ε) ℂ)),
      Commute (if a = c then 1 else 0) T := by
    intro a c T
    split_ifs <;> simp
  refine ⟨fun c d => ∑ i : NC ε, yy i * (u i.1.1 c * v d i.1.2), ?_, ?_, ?_⟩
  · intro c d e f
    refine glRel_abstract yy u v ?_ ?_ ?_ ?_ ?_ ?_ ?_ c d e f
    · intro i j
      refine LinearMap.ext fun f => ?_
      simp [yy, mul_left_comm]
    · intro a b c d
      exact (hδ _ _ _).sub_left ((hδ _ _ _).symm.sub_right (dd_comm _ _ _ _))
    · intro a b c d
      exact (hδ _ _ _).sub_left ((hδ _ _ _).symm.add_right (dd_comm _ _ _ _))
    · intro a b c d
      exact (hδ _ _ _).add_left ((hδ _ _ _).symm.add_right (dd_comm _ _ _ _))
    · intro a c j
      rw [← dd_yy]
      simp only [u, sub_mul, mul_sub, (hδ a c (yy j)).eq]
      abel
    · intro a c j
      rw [← dd_yy]
      simp only [v, add_mul, mul_add, (hδ a c (yy j)).eq]
      abel
    · intro d e
      have h0 : ¬(ε d = true ∧ ε e = false) → dd ε d e = 0 := fun h => dif_neg h
      simp only [u, v]
      generalize dd ε d e = T at *
      by_cases hde : d = e
      · subst hde
        cases h : ε d <;> simp_all
      · cases h : ε d <;> cases h' : ε e <;> simp_all
  · intro i f
    have hu : ∀ j : NC ε, u j.1.1 i.1.1 = if j.1.1 = i.1.1 then 1 else 0 := by
      intro j
      simp [u, dd, i.2.1]
    have hv : ∀ j : NC ε, v i.1.2 j.1.2 = if i.1.2 = j.1.2 then 1 else 0 := by
      intro j
      simp [v, dd, i.2.2]
    simp only [hu, hv]
    rw [Finset.sum_eq_single i]
    · simp [yy]
    · intro j _ hj
      split_ifs with h1 h2
      · exact absurd (Subtype.ext (Prod.ext h1 h2.symm)) hj
      all_goals simp
    · simp
  · intro a b f
    set_option synthInstance.maxHeartbeats 100000 in
      simp [yy, LinearMap.sum_apply, map_sum]

end GlobalTheory.CompanionTheory.DSVerma
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NotCdomAddRoot
section
open Finset

namespace GlobalTheory.CompanionTheory.DSHighestOfKType

open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)

variable {n : ℕ}

theorem height_root (a b : Fin n) : ∑ i : Fin n, ((i : ℕ) : ℝ) * root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem not_cdom_add_root (ε : Fin n → Bool) (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ CDom ε (μ + root a b) μ := by
  rintro ⟨c, hc, h⟩
  have h1 : ∑ i : Fin n, ((i : ℕ) : ℝ) * (μ - (μ + root a b)) i = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    have : ∀ i : Fin n, ((i : ℕ) : ℝ) * (μ - (μ + root a b)) i = -(((i : ℕ) : ℝ) * root a b i) := by
      intro i; simp
    simp only [this, Finset.sum_neg_distrib, height_root]; ring
  have h2 : ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ x, ∑ y, (c x y : ℝ) • root x y) i
      = ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) := by
    simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h3 : ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have hxy : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast (hc x y h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  rw [h, h2] at h1
  linarith

theorem isWeight_apply {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {μ : Fin n → ℝ} {v : V} (hv : IsWeight E μ v) (a b : Fin n) :
    IsWeight E (μ + root a b) (E a b v) := by
  intro c
  have h := LinearMap.congr_fun (hE c c a b) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [root]
  · subst h1; simp [root, h2, Ne.symm h2, add_smul, add_comm]
  · subst h2; simp [root, h1, add_smul, add_comm]
  · simp [root, h1, h2, Ne.symm h2]

theorem hwOfType : CompanionTheory.D.DSIC.StabLink → CompanionTheory.D.DSIC.WtLink → CompanionTheory.D.DSIC.HWofType := by
  intro hS hW n ε H _ _ σ S E hσ hm μ T hT hTS
  obtain ⟨hfin, hst, -, ⟨v, hvT, hv0, hvw⟩, hdom⟩ := hT
  have hmap : (T.comap S.subtype).map S.subtype = T := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hTS
  have hfinU : FiniteDimensional ℂ (T.comap S.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hTS).symm.finiteDimensional
  have hU := (hS n ε H σ S E hσ hm _ hfinU).2 (by rw [hmap]; exact hst)
  have hw : IsWeight E μ (⟨v, hTS hvT⟩ : S) := (hW n ε H σ S E hσ hm μ _).2 hvw
  refine ⟨⟨v, hTS hvT⟩, fun h => hv0 (congrArg Subtype.val h), hvT, hw, fun a b hab hε => ?_⟩
  by_contra hne
  have hmem := hU a b hε ⟨v, hTS hvT⟩ hvT
  have hw' := (hW n ε H σ S E hσ hm _ _).1 (isWeight_apply hm.gl hw a b)
  exact not_cdom_add_root ε μ hab (hdom _ _ hmem (fun h => hne (Subtype.ext h)) hw')

end GlobalTheory.CompanionTheory.DSHighestOfKType
end

