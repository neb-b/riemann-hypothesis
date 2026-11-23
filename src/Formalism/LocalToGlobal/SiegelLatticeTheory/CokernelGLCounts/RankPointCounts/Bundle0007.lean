module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxGen

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOneEqOne
section
noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

def lawX {ι P : Type} (BX : P → (P → ℂ) → (P → ℂ) → ℂ) (γ x : ι → P → ℂ) : ι → P → ℂ :=
  fun v p => γ v p + x v p + BX p (γ v) (x v)

theorem pi_measure_eq_prod_absNorm_mul_sqrt_discr (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBm : ∀ p, Measurable (fun z : (P → ℂ) × (P → ℂ) => BX p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (hB0 : ∀ p (x : P → ℂ), BX p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (hinv : ∀ γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : ι → P → ℂ,
      (∀ p, (fun v => γ' v p) - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧
        ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x)
    (Kset : Set (ι → P → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ x, ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧
      lawX BX γ x ∈ Kset) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : P => ENNReal.ofReal c • (volume : Measure ℂ)) Kset =
      ∏ p, ENNReal.ofReal (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) := by
  have hsf : SigmaFinite (ENNReal.ofReal c • (volume : Measure ℂ)) :=
    (inferInstance : SigmaFinite (c.toNNReal • (volume : Measure ℂ)))
  let sw : (ι → P → ℂ) → (P → ι → ℂ) := fun x p v => x v p
  let usw : (P → ι → ℂ) → (ι → P → ℂ) := fun y v p => y p v
  have h1 : ∀ x, usw (sw x) = x := fun x => rfl
  have h2 : ∀ y, sw (usw y) = y := fun y => rfl
  have hsw : MeasurePreserving sw _ _ := swap_mp (ι := ι) (P := P) (ENNReal.ofReal c • (volume : Measure ℂ))
  have husw : Measurable usw :=
    Measurable.of_eval fun v => Measurable.of_eval fun p =>
      (measurable_pi_apply v).comp (measurable_pi_apply p)
  let B : ∀ _ : P, (P → ι → ℂ) → (P → ι → ℂ) → (ι → ℂ) := fun p y y' v => BX p (fun q => y q v) (fun q => y' q v)
  let τT : ∀ _ : P, (P → ι → ℂ) → (ι → ℂ) := fun p y => τ p (usw y)
  have hlaw : ∀ γ x, mlaw B (sw γ) (sw x) = sw (lawX BX γ x) := fun γ x => rfl
  have hmemT : ∀ γ : ι → P → ℂ, (∀ p, sw γ p - τT p (sw γ) ∈ (Λ p).map (embS φ (s p))) ↔
      (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) := fun γ => Iff.rfl
  have hpre : Kset = sw ⁻¹' (usw ⁻¹' Kset) := by ext x; simp [h1]
  have hKT : MeasurableSet (usw ⁻¹' Kset) := husw hK
  rw [hpre, hsw.measure_preimage hKT.nullMeasurableSet]
  refine covol_oneT K ι φ σ hφ P h B ?_ ?_ ?_ c hc I Λ hΛ k hk hk0 s hs τT ?_ ?_ (usw ⁻¹' Kset) hKT ?_
  · intro p
    refine Measurable.of_eval fun v => ?_
    have hf : Measurable (fun z : (P → ι → ℂ) × (P → ι → ℂ) => ((fun q => z.1 q v), (fun q => z.2 q v))) :=
      (Measurable.of_eval fun q => (measurable_pi_apply v).comp ((measurable_pi_apply q).comp measurable_fst)).prodMk
        (Measurable.of_eval fun q => (measurable_pi_apply v).comp ((measurable_pi_apply q).comp measurable_snd))
    exact (hBm p).comp hf
  · intro p x x' y y' hxy
    funext v
    exact hBd p _ _ _ _ fun q hq => ⟨congrFun (hxy q hq).1 v, congrFun (hxy q hq).2 v⟩
  · intro p x
    funext v
    exact hB0 p _
  · intro p x x' hxx
    exact hτ p _ _ fun q hq v => congrFun (hxx q hq) v
  · intro γT hγT
    obtain ⟨γ', hγ', hinv'⟩ := hinv (usw γT) ((hmemT (usw γT)).1 (by rw [h2]; exact hγT))
    refine ⟨sw γ', (hmemT γ').2 hγ', fun g => ⟨?_, ?_⟩⟩
    · have := (hinv' (usw g)).1
      calc mlaw B (sw γ') (mlaw B γT g) = mlaw B (sw γ') (mlaw B (sw (usw γT)) (sw (usw g))) := by rw [h2, h2]
        _ = sw (lawX BX γ' (lawX BX (usw γT) (usw g))) := by rw [hlaw, hlaw]
        _ = g := by rw [this, h2]
    · have := (hinv' (usw g)).2
      calc mlaw B γT (mlaw B (sw γ') g) = mlaw B (sw (usw γT)) (mlaw B (sw γ') (sw (usw g))) := by rw [h2, h2]
        _ = sw (lawX BX (usw γT) (lawX BX γ' (usw g))) := by rw [hlaw, hlaw]
        _ = g := by rw [this, h2]
  · intro g
    obtain ⟨γ, ⟨hγΓ, hγK⟩, hγu⟩ := hKd (usw g)
    refine ⟨sw γ, ⟨(hmemT γ).2 hγΓ, ?_⟩, ?_⟩
    · show usw (mlaw B (sw γ) g) ∈ Kset
      rw [show g = sw (usw g) from (h2 g).symm, hlaw, h1]; exact hγK
    · rintro γT ⟨hΓT, hKT'⟩
      have e := hγu (usw γT) ⟨(hmemT (usw γT)).1 (by rw [h2]; exact hΓT), by
        have : usw (mlaw B γT g) ∈ Kset := hKT'
        rw [show γT = sw (usw γT) from (h2 γT).symm, show g = sw (usw g) from (h2 g).symm, hlaw, h1] at this
        exact this⟩
      rw [← e, h2]

theorem covol_one_eq_one (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBm : ∀ p, Measurable (fun z : (P → ℂ) × (P → ℂ) => BX p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (hB0 : ∀ p (x : P → ℂ), BX p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (hconst : ∏ p, (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) = 1)
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (hinv : ∀ γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : ι → P → ℂ,
      (∀ p, (fun v => γ' v p) - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧
        ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x)
    (Kset : Set (ι → P → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ x, ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧
      lawX BX γ x ∈ Kset) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : P => ENNReal.ofReal c • (volume : Measure ℂ)) Kset = 1 := by
  rw [pi_measure_eq_prod_absNorm_mul_sqrt_discr K ι φ σ hφ P h BX hBm hBd hB0 c hc I Λ hΛ k hk hk0 s hs τ hτ hinv Kset hK hKd,
    ← ENNReal.ofReal_prod_of_nonneg, hconst, ENNReal.ofReal_one]
  intro p _
  have hN := FractionalIdeal.absNorm_nonneg (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  have hN' : (0 : ℝ) ≤ (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) := by
    exact_mod_cast hN
  positivity

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxLoc
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Loc

open Formalism.MainNotions.S.Loc PI.StrongApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} (L : LocAt F E sig p)

def latS (c : L.Fp) : AddSubgroup L.Ep where
  carrier := {x | ∃ y ∈ L.O, x = algebraMap L.Fp L.Ep c * y}
  zero_mem' := ⟨0, L.O.zero_mem, by simp⟩
  add_mem' := by
    rintro x x' ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', L.O.add_mem hy hy', by ring⟩
  neg_mem' := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, L.O.neg_mem hy, by ring⟩

variable {L}

theorem mem_latS {c : L.Fp} {x : L.Ep} : x ∈ latS L c ↔ ∃ y ∈ L.O, x = algebraMap L.Fp L.Ep c * y := Iff.rfl

theorem alg_mem_O {s : L.Fp} (hs : s ∈ 𝒪[L.Fp]) : algebraMap L.Fp L.Ep s ∈ L.O := by
  refine (L.O_def _).mpr ?_
  first
  | exact isIntegral_algebraMap (x := (⟨s, hs⟩ : 𝒪[L.Fp]))
  | exact (IsScalarTower.algebraMap_apply (𝒪[L.Fp]) L.Fp L.Ep ⟨s, hs⟩) ▸ isIntegral_algebraMap

theorem latS_mul {c c' : L.Fp} {x y : L.Ep} (hx : x ∈ latS L c) (hy : y ∈ latS L c') : x * y ∈ latS L (c * c') := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, L.O.mul_mem ha hb, by rw [map_mul]; ring⟩

theorem O_mul_latS {c : L.Fp} {x y : L.Ep} (hy : y ∈ L.O) (hx : x ∈ latS L c) : y * x ∈ latS L c := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨y * a, L.O.mul_mem hy ha, by ring⟩

theorem latS_mono {c c' : L.Fp} (hc' : c' ∈ 𝒪[L.Fp]) {x : L.Ep} (hx : x ∈ latS L (c * c')) : x ∈ latS L c := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨algebraMap L.Fp L.Ep c' * a, L.O.mul_mem (alg_mem_O hc') ha, by rw [map_mul]; ring⟩

theorem bounded_Fp (a : L.Fp) : ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ s * a ∈ 𝒪[L.Fp] := by
  by_cases ha : a ∈ 𝒪[L.Fp]
  · exact ⟨1, one_ne_zero, one_mem _, by rw [one_mul]; exact ha⟩
  · have h0 : a ≠ 0 := by
      rintro rfl
      exact ha (zero_mem _)
    refine ⟨a⁻¹, inv_ne_zero h0, ?_, by rw [inv_mul_cancel₀ h0]; exact one_mem _⟩
    rw [Valuation.mem_integer_iff] at ha ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp ha))

theorem bounded (x : L.Ep) : ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ algebraMap L.Fp L.Ep s * x ∈ L.O := by
  classical
  obtain ⟨n, b, hbint, hbspan⟩ := intSpan' F E
  obtain ⟨α, hα⟩ := local_span_holds F E sig p L n b hbspan x
  choose s hs0 hsO hsa using fun i => bounded_Fp (L := L) (α i)
  have hbO : ∀ i, L.ιE (b i) ∈ L.O := by
    intro i
    have := local_integral_of_substitution F E sig p L 1 (b i) (by simp) (hbint i)
    simpa using this
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.2 fun i _ => hs0 i, Subring.prod_mem _ fun i _ => hsO i, ?_⟩
  rw [hα, Finset.mul_sum]
  refine L.O.sum_mem fun i _ => ?_
  have e : algebraMap L.Fp L.Ep (∏ j, s j) * (α i • L.ιE (b i)) =
      algebraMap L.Fp L.Ep ((∏ j ∈ Finset.univ.erase i, s j) * (s i * α i)) * L.ιE (b i) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    ring_nf
  rw [e]
  exact L.O.mul_mem (alg_mem_O (Subring.mul_mem _ (Subring.prod_mem _ fun j _ => hsO j) (hsa i))) (hbO i)

theorem bounded_mat {n : ℕ} (B : Matrix (Fin n) (Fin n) L.Ep) :
    ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O := by
  choose s hs0 hsO hsB using fun (p : Fin n × Fin n) => bounded (B p.1 p.2)
  refine ⟨∏ p, s p, Finset.prod_ne_zero_iff.mpr fun p _ => hs0 p, prod_mem fun p _ => hsO p, ?_⟩
  intro i j
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ (i, j)), map_mul, mul_comm (algebraMap L.Fp L.Ep (s (i, j))), mul_assoc]
  exact L.O.mul_mem (alg_mem_O (prod_mem fun p _ => hsO p)) (hsB (i, j))

theorem entIn_mul_left {n : ℕ} {B : Matrix (Fin n) (Fin n) L.Ep} {s : L.Fp}
    (hs : ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O) {c : L.Fp} {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L (s * c)) X) : EntIn (latS L c) (B * X) := by
  intro i j
  rw [Matrix.mul_apply]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  obtain ⟨y, hy, hxy⟩ := hX k j
  refine ⟨algebraMap L.Fp L.Ep s * B i k * y, L.O.mul_mem (hs i k) hy, ?_⟩
  rw [hxy, map_mul]
  ring

theorem entIn_mul_right {n : ℕ} {B : Matrix (Fin n) (Fin n) L.Ep} {s : L.Fp}
    (hs : ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O) {c : L.Fp} {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L (s * c)) X) : EntIn (latS L c) (X * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  obtain ⟨y, hy, hxy⟩ := hX i k
  refine ⟨algebraMap L.Fp L.Ep s * B k j * y, L.O.mul_mem (hs k j) hy, ?_⟩
  rw [hxy, map_mul]
  ring

theorem latS_mul_self {c : L.Fp} (hc : c ∈ 𝒪[L.Fp]) {x y : L.Ep} (hx : x ∈ latS L c) (hy : y ∈ latS L c) :
    x * y ∈ latS L c := latS_mono hc (latS_mul hx hy)

end Loc

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxMono
section
noncomputable section

namespace Formalism.L2.SG.Pf.ProdEApprox

section Mono

variable {A : Type*} [CommRing A] {n : ℕ}

def mono (σ : Fin n → Fin n) (ν : Fin n → A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => if b = σ a then ν a else 0

theorem mono_mul (σ : Fin n → Fin n) (ν : Fin n → A) (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (mono σ ν * X) i j = ν i * X (σ i) j := by
  simp [mono, Matrix.mul_apply, ite_mul]

variable {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) (ν : Fin n → A)
include hσ

theorem mul_mono (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) : (X * mono σ ν) i j = X i (σ j) * ν (σ j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · simp [mono, hσ]
  · intro b _ hb
    have hj : j ≠ σ b := fun h => hb (by rw [h, hσ])
    simp [mono, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fix_entry {l c : Matrix (Fin n) (Fin n) A} (h : l * mono σ ν = mono σ ν * c) (i j : Fin n) :
    l i j * ν j = ν i * c (σ i) (σ j) := by
  have e := congrFun (congrFun h i) (σ j)
  rw [mul_mono hσ, mono_mul, hσ] at e
  exact e

theorem fix_pat (hν : ∀ a, IsUnit (ν a)) {l c : Matrix (Fin n) (Fin n) A} (hc : ∀ i j, j < i → c i j = 0)
    (h : l * mono σ ν = mono σ ν * c) (i j : Fin n) (hij : σ j < σ i) : l i j = 0 := by
  have e := fix_entry hσ ν h i j
  rw [hc _ _ hij, mul_zero] at e
  exact (hν j).mul_left_eq_zero.mp e


omit hσ in
def cOf (σ : Fin n → Fin n) (ν : Fin n → A) (l : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => Ring.inverse (ν (σ a)) * l (σ a) (σ b) * ν (σ b)

theorem fix_cOf (hν : ∀ a, IsUnit (ν a)) (l : Matrix (Fin n) (Fin n) A) :
    l * mono σ ν = mono σ ν * cOf σ ν l := by
  ext i j
  rw [mul_mono hσ, mono_mul]
  simp only [cOf, Matrix.of_apply, hσ]
  rw [← mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ (hν i), one_mul]

theorem cOf_up (l : Matrix (Fin n) (Fin n) A) (hl : ∀ i, l i i = 1) (hpat : ∀ i j, σ j < σ i → l i j = 0)
    (hν : ∀ a, IsUnit (ν a)) : (∀ a, cOf σ ν l a a = 1) ∧ ∀ a b, b < a → cOf σ ν l a b = 0 := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp only [cOf, Matrix.of_apply, hl, mul_one]
    exact Ring.inverse_mul_cancel _ (hν _)
  · simp only [cOf, Matrix.of_apply]
    rw [hpat (σ a) (σ b) (by rw [hσ, hσ]; exact hab), mul_zero, zero_mul]

end Mono

end Formalism.L2.SG.Pf.ProdEApprox
end
end

