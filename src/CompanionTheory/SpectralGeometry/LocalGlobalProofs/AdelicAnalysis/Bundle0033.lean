module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjections
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryFiniteSetDecomposition
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PureH

theorem map_consTup {K L : Type} [Zero K] [One K] [Zero L] [One L] (f : K → L) (h0 : f 0 = 0)
    (h1 : f 1 = 1) {M n : ℕ} (X : Fin n → Fin M → K) :
    (fun a i => f (consTup X a i)) = consTup (fun a i => f (X a i)) := by
  funext a i
  induction a using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simp [consTup, h1]
    | succ i => simp [consTup, h0]
  | succ a =>
    induction i using Fin.cases with
    | zero => simp [consTup, h0]
    | succ i => simp [consTup]

theorem consTup_empty {K : Type} [Zero K] [One K] {M : ℕ} (X : Fin 0 → Fin M → K) :
    (consTup X : Fin (0 + 1) → Fin (M + 1) → K) = fun _ : Fin 1 => Fin.cons 1 (fun _ => 0) := by
  funext a
  induction a using Fin.cases with
  | zero => simp [consTup]
  | succ a => exact a.elim0

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem projInf_consTup {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) :
    projInf (consTup X) = consTup (projInf X) :=
  map_consTup (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (map_zero _) (map_one _) X

theorem projFin_consTup {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) :
    projFin (consTup X) = consTup (projFin X) :=
  map_consTup (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (map_zero _) (map_one _) X

theorem projV_consTup (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (consTup X) = consTup (projV v X) :=
  map_consTup (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) (map_zero _) (map_one _) X

theorem consTup_mem_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ}
    (h0 : ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) : consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro h a i k
    simpa [consTup] using h a.succ i.succ k
  · intro h a i k
    induction a using Fin.cases with
    | zero => simpa [consTup] using h0 (fun a => a.elim0) 0 i k
    | succ a =>
      induction i using Fin.cases with
      | zero => simp [consTup, zero_mem]
      | succ i => simpa [consTup] using h a i k

end Glob

end GlobalTheory.CompanionTheory.SW.PureH

namespace GlobalTheory.CompanionTheory.SW.PureH

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  [DecidableEq (HeightOneSpectrum (𝓞 F))]

theorem prod_union_split {ι : Type} [DecidableEq ι] (S Sh : Finset ι) (A B : ι → ℝ≥0∞) (P : ι → Prop)
    [DecidablePred P] (hS : ∀ v, P v ↔ v ∈ S) :
    ∏ v ∈ S ∪ Sh, (if P v then A v else B v) = (∏ v ∈ S, A v) * ∏ v ∈ Sh \ S, B v := by
  rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => if_pos ((hS v).2 hv)
  · exact Finset.prod_congr rfl fun v hv => if_neg fun h => (Finset.mem_sdiff.1 hv).2 ((hS v).1 h)

variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
  (Jp : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA (AF F) σ Jp) (ginf : HA (Ainf F) σ Jp)
  (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ Jp) (S Sh : Finset (HeightOneSpectrum (𝓞 F)))


include b in
theorem pureL_act
    (hinf : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E),
      projInf (actW (AF F) σ Jp h X) = actW (Ainf F) σ Jp ginf (projInf X))
    (hfin : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      projV v (projFin (actW (AF F) σ Jp h X)) = actW (Fv F v) σ Jp (g v) (projV v (projFin X)))
    (hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ Jp (g v) X ∈ latV b v ↔ X ∈ latV b v)
    (hS : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    {n : ℕ} (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b S φinf φ (actW (AF F) σ Jp h (consTup X)) =
      pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ Jp ginf (consTup Y)))
        (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ Jp (g v) (consTup Y))
          else (latV b v).indicator 1 (actW (Fv F v) σ Jp (g v) (consTup Y))) X := by
  have hP : projInf (actW (AF F) σ Jp h (consTup X)) =
      actW (Ainf F) σ Jp ginf (consTup (projInf X)) := by
    rw [hinf, projInf_consTup]
  have hV : ∀ v, projV v (projFin (actW (AF F) σ Jp h (consTup X))) =
      actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) := fun v => by
    rw [hfin, projFin_consTup, projV_consTup]
  have key : ∀ v, v ∉ S → v ∉ Sh →
      (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) ∈ latV b v ↔
        projV v (projFin X) ∈ latV b v) := fun v h1 h2 =>
    (hSh v h2 _ _).trans (consTup_mem_latV b v (hS v h1) _)
  have hprod := prod_union_split S Sh
    (fun v => φ v (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))))
    (fun v => ((latV b v).indicator 1 (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))) : ℝ≥0∞))
    (fun v => v ∈ S) (fun _ => Iff.rfl)
  unfold pureL
  by_cases hX : X ∈ intOff b (S ∪ Sh)
  · rw [Set.indicator_of_mem hX, hprod]
    by_cases hA : ∀ v ∈ Sh \ S, actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) ∈ latV b v
    · have hY : actW (AF F) σ Jp h (consTup X) ∈ intOff b S := by
        intro v hv
        rw [hV]
        by_cases hvh : v ∈ Sh
        · exact hA v (Finset.mem_sdiff.2 ⟨hvh, hv⟩)
        · exact (key v hv hvh).2 (hX v (by simp [hv, hvh]))
      rw [Set.indicator_of_mem hY, hP, Finset.prod_eq_one
        (f := fun v => ((latV b v).indicator 1
          (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))) : ℝ≥0∞))
        (fun v hv => by simp [Set.indicator_of_mem (hA v hv)])]
      simp only [mul_one, hV]
    · push Not at hA
      obtain ⟨v, hv, hvl⟩ := hA
      have hY : actW (AF F) σ Jp h (consTup X) ∉ intOff b S := by
        intro hm
        have := hm v (Finset.mem_sdiff.1 hv).2
        rw [hV] at this
        exact hvl this
      rw [Set.indicator_of_notMem hY, Finset.prod_eq_zero hv (by simp [Set.indicator_of_notMem hvl])]
      simp
  · have hY : actW (AF F) σ Jp h (consTup X) ∉ intOff b S := by
      intro hm
      apply hX
      intro v hv
      have hv' : v ∉ S ∧ v ∉ Sh := by simpa using hv
      have := hm v hv'.1
      rw [hV] at this
      exact (key v hv'.1 hv'.2).1 this
    rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hY]


include b in
theorem pureL_act_vec
    (hinf : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E),
      projInf (actW (AF F) σ Jp h X) = actW (Ainf F) σ Jp ginf (projInf X))
    (hfin : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      projV v (projFin (actW (AF F) σ Jp h X)) = actW (Fv F v) σ Jp (g v) (projV v (projFin X)))
    (hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ Jp (g v) X ∈ latV b v ↔ X ∈ latV b v)
    (hS : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) :
    pureL b S Ψinf Ψ (actW (AF F) σ Jp h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) =
      (Ψinf (actW (Ainf F) σ Jp ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) *
        ∏ v ∈ S, Ψ v (actW (Fv F v) σ Jp (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) *
        ∏ v ∈ Sh \ S, (latV b v).indicator 1
          (actW (Fv F v) σ Jp (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  let X₀ : Fin 0 → Fin M → AF F ⊗[F] E := fun a => a.elim0
  have h1 := pureL_act (n := 0) b σ Jp h ginf g S Sh hinf hfin hSh hS Ψinf Ψ X₀
  have hmem : X₀ ∈ intOff b (S ∪ Sh) := fun v _ a => a.elim0
  unfold pureL at h1
  rw [Set.indicator_of_mem hmem] at h1
  rw [consTup_empty] at h1
  simp only [consTup_empty] at h1
  rw [prod_union_split S Sh _ _ (fun v => v ∈ S) (fun _ => Iff.rfl)] at h1
  rw [mul_assoc]
  unfold pureL
  exact h1

end Core

theorem pure_h : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ∃ (ginf : HA (Ainf F) σ (blockOne (algebraMap F E t) J)) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ (blockOne (algebraMap F E t) J)) (Sh : Finset (HeightOneSpectrum (𝓞 F))), ∀ S, S₁ ⊆ S → (∀ (n : ℕ) (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (X : Fin n → Fin M → AF F ⊗[F] E), pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) = pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ _ ginf (consTup Y))) (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) X) ∧ ∀ (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) = (Ψinf (actW (Ainf F) σ _ ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) * ∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  intro F E _ _ _ _ _ _ σ hCM M J hJ t ht d b
  have hba := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hba.2.1 hJ.1, by
      rw [hba.1]
      exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2⟩
  obtain ⟨pinf, p, hcomp, hlat, -⟩ := GlobalTheory.CompanionTheory.SW.HProj.components F E σ hCM (M + 1) _ hJ'
  have hcons := (GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hCM d b 0 M).2.2
  let S₁ : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hcons).toFinset
  refine ⟨S₁, fun h => ?_⟩
  have hlat' := hlat d b h
  let Sh : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hlat').toFinset
  have hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ _ (p v h) X ∈ latV b v ↔ X ∈ latV b v := fun v hv => by
    simpa [Sh] using hv
  refine ⟨pinf h, fun v => p v h, Sh, fun S hS => ?_⟩
  have hS' : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v := by
    intro v hv X₀
    have hv₁ : v ∉ S₁ := fun hm => hv (hS hm)
    have : ∀ X : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X ∈ latV b v ↔ X ∈ latV b v := by
      simpa [S₁] using hv₁
    exact (this X₀).2 fun a => a.elim0
  have hinf := fun (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) => (hcomp n h X).1
  have hfin := fun (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)) =>
    (hcomp n h X).2 v
  exact ⟨fun n φinf φ X => pureL_act b σ _ h (pinf h) (fun v => p v h) S Sh hinf hfin hSh hS' φinf φ X,
    fun Ψinf Ψ => pureL_act_vec b σ _ h (pinf h) (fun v => p v h) S Sh hinf hfin hSh hS' Ψinf Ψ⟩

end GlobalTheory.CompanionTheory.SW.PureH
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanLocalDensityFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.InfDens

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R]
  [Algebra F R]

theorem sigR_sigR (hs : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [sigR, hs]
  | add a c ha hc => rw [map_add (f := _), map_add (f := _), ha, hc]

theorem sigR_inclR (y : E) : sigR R σ (inclR R y) = inclR R (σ y) := by
  simp [sigR, inclR]

theorem sigR_hR (hs : ∀ x, σ (σ x) = x) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R hs, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gramR_mem (hs : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := fun a c => sigR_hR R hs hJ (X c) (X a)

end Alg

section Real

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem e_half_trace {σ : E →ₐ[F] E} {M d : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → Ainf F ⊗[F] E,
      Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) =
        cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y))
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) :
    e (algebraMap F (Ainf F) (1 / 2) *
        Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (gramR (Ainf F) σ J X 0 0)) w =
      (1 / 2 : ℝ) * (xw e b X w ⬝ᵥ (B.map (ρ w) *ᵥ xw e b X w)) := by
  let ew : Ainf F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (e : Ainf F →+* _)
  have hew : ∀ a, ew a = e a w := fun _ => rfl
  have hcomp : ew.comp (algebraMap F (Ainf F)) = ρ w := RingHom.ext fun x => hρ x w
  have hx : xw e b X w = ew ∘ cv (Ainf F) b (X 0) := rfl
  have hm : B.map (ρ w) = (B.map (algebraMap F (Ainf F))).map ew := by
    rw [← hcomp]
    ext i j
    rfl
  have hhalf : ρ w (1 / 2) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [← hew, map_mul, hew, hρ, hhalf]
  show _ * ew (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J (X 0) (X 0))) = _
  rw [hB, hx, hm, RingHom.map_dotProduct]
  have hv : ⇑ew ∘ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b (X 0)) =
      (B.map (algebraMap F (Ainf F))).map ew *ᵥ (⇑ew ∘ cv (Ainf F) b (X 0)) :=
    funext fun i => RingHom.map_mulVec ew _ _ i
  rw [hv]

end Real

theorem infDens : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Ainf F ⊗[F] E, Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) = cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → ∀ Dinf : (InfinitePlace F → ℝ) → ℝ, Continuous Dinf → (∀ y, 0 ≤ Dinf y) → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → Fin M × Fin d → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) → ∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X) ∂(coordW (Ainf F) b laminf 1 M) = ∫⁻ S in U, ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)))) ∂(coordHerm (Ainf F) σ b laminf 1) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM d b B hB ρ e he hρ Pm laminf hlam hmap Dinf hDc hD0 hDinf U hU
  obtain ⟨i1, i2, i3, i4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩
  haveI : SigmaFinite laminf := inferInstance
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at h1
    simpa using h1.symm
  have hs : ∀ x, σ (σ x) = x := HermOne.sig_sig hcm
  set κ : ℝ := (Real.sqrt |(discr F : ℝ)|)⁻¹ with hκ
  have hκ0 : 0 ≤ κ := inv_nonneg.2 (Real.sqrt_nonneg _)

  let tt := HermOne.hermHomeo (Ainf F) (σ := σ) hcm
  let eH : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph e
  let τ : HermR (Ainf F) σ 1 ≃ₜ (InfinitePlace F → ℝ) := tt.trans eH
  have hτ : ∀ S, τ S = e (algebraMap F (Ainf F) (1 / 2) *
      Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)) :=
    fun _ => rfl
  have hpush : (coordHerm (Ainf F) σ b laminf 1).map τ = ENNReal.ofReal κ • volume := by
    have h1 : (τ : HermR (Ainf F) σ 1 → _) = e ∘ tt := rfl
    rw [h1, ← Measure.map_map (f := tt) (g := e) eH.measurable tt.measurable,
      HermOne.map_coordHerm (Ainf F) hcm b laminf, hmap]
  set U' : Set (InfinitePlace F → ℝ) := τ.symm ⁻¹' U with hU'def
  have hU' : MeasurableSet U' := τ.symm.measurable hU
  have hpre : τ ⁻¹' U' = U := by
    ext S
    simp [hU'def]

  have hR1 : ∫⁻ S in U, ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) *
        Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))))
        ∂(coordHerm (Ainf F) σ b laminf 1) =
      ENNReal.ofReal (κ ^ (2 * M)) * ∫⁻ y in U', ENNReal.ofReal (Dinf y) := by
    have h2 := setLIntegral_map (μ := coordHerm (Ainf F) σ b laminf 1) (g := τ)
      (f := fun y => ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf y)) hU'
      (continuous_const.mul hDc).measurable.ennreal_ofReal τ.measurable
    rw [hpre, hpush] at h2
    simp only [hτ] at h2
    rw [← h2, Measure.restrict_smul, lintegral_smul_measure]
    have h3 : ∀ y, ENNReal.ofReal (κ ^ (2 * M - 1) * Dinf y) =
        ENNReal.ofReal (κ ^ (2 * M - 1)) * ENNReal.ofReal (Dinf y) :=
      fun y => ENNReal.ofReal_mul (pow_nonneg hκ0 _)
    simp only [h3]
    rw [lintegral_const_mul _ (hDc.measurable.ennreal_ofReal), smul_eq_mul, ← mul_assoc,
      ← ENNReal.ofReal_mul hκ0, ← pow_succ', show 2 * M - 1 + 1 = 2 * M by omega]

  let Φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → (InfinitePlace F → Fin M × Fin d → ℝ) :=
    fun X w => xw e b X w
  have hcoord := (_root_.GlobalTheory.CompanionTheory.SW.BB.coordMap_one F E σ hcm (Ainf F) d b laminf hlam M).2.1
  have hΦm : Measurable Φ := by
    have hc : Continuous fun (z : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) =>
        e (z p) w :=
      continuous_pi fun w => continuous_pi fun p =>
        (continuous_apply w).comp (eH.continuous.comp (continuous_apply p))
    exact hc.measurable.comp hcoord.measurable
  have hpushL := _root_.GlobalTheory.CompanionTheory.SW.BB.infPush F E σ hcm M d b e he laminf hlam hmap
  let Q : (InfinitePlace F → Fin M × Fin d → ℝ) → (InfinitePlace F → ℝ) :=
    fun x w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))
  have hQc : Continuous Q := by
    refine continuous_pi fun w => continuous_const.mul ?_
    exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
  let G : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w)))
  have hGm : Measurable G := by
    have hc : Continuous fun x : InfinitePlace F → Fin M × Fin d → ℝ =>
        Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w)) := by
      refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
      exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
    exact hc.measurable.ennreal_ofReal
  have hset : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U) = Φ ⁻¹' (Q ⁻¹' U') := by
    ext X
    have hmem := gramR_mem (Ainf F) hs hJ.1 X
    have hQ : Q (Φ X) = τ ⟨gramR (Ainf F) σ J X, hmem⟩ := by
      funext w
      rw [hτ]
      exact (e_half_trace b B hB ρ e hρ X w).symm
    simp only [Set.mem_preimage, hU'def]
    rw [hQ, Homeomorph.symm_apply_apply]
    constructor
    · rintro ⟨S, hS, hSX⟩
      have : (⟨gramR (Ainf F) σ J X, hmem⟩ : HermR (Ainf F) σ 1) = S := Subtype.ext hSX.symm
      rwa [this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hL1 : ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X)
        ∂(coordW (Ainf F) b laminf 1 M) =
      ENNReal.ofReal (κ ^ (M * d)) * ∫⁻ y in U', ENNReal.ofReal (Dinf y) := by
    have hA : MeasurableSet (Q ⁻¹' U') := hQc.measurable hU'
    have h2 := setLIntegral_map (μ := coordW (Ainf F) b laminf 1 M) hA hGm hΦm
    rw [hset]
    have h3 : ∀ X, ENNReal.ofReal (gaussQ e b Pm X) = G (Φ X) := fun _ => rfl
    simp only [h3]
    rw [← h2]
    have h4 : (coordW (Ainf F) b laminf 1 M).map Φ =
        ENNReal.ofReal (κ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ)) :=
      hpushL
    rw [h4, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    exact congrArg _ (hDinf U' hU')
  rw [hL1, hR1, hd, mul_comm M 2]

end GlobalTheory.CompanionTheory.SW.BB.InfDens
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDisintegration
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem lintegral_fibS_of_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ S hS
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨hKR, hKLC, hKSC, hKT2, -, -, -, hKB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  have := hKR
  have := hKLC
  have := hKSC
  have := hKT2
  obtain ⟨-, -, hHSC, -, hHB, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJ' R
  have := hHSC
  have := hHB
  have := hKB (n + 1) (M + 1)
  have k₁ := (_root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁).2.1
  have k' := (_root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm').2.1
  have hact' := (hact (n + 1)).1
  have := k₁ (hermScal R σ (algebraMap F R t))
  have := k' (schur R σ t a S)
  have hvec : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E),
      Measurable (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X) := by
    intro A c
    refine Measurable.of_eval (fun i => ?_)
    induction i using Fin.cases with
    | zero =>
      have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X 0) =
          fun _ => Fin.cons A (fun _ => 0) := rfl
      rw [h0]
      exact measurable_const
    | succ j =>
      refine Measurable.of_eval (fun k => ?_)
      induction k using Fin.cases with
      | zero =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ 0) = fun _ => c j := rfl
        rw [h0]
        exact measurable_const
      | succ l =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ l.succ) =
            fun X => X j l := rfl
        rw [h0]
        exact (measurable_pi_apply l).comp (measurable_pi_apply j)
  have hf : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2)) := fun A c =>
    hact'.measurable.comp ((D.hs.comp measurable_fst).prodMk ((hvec A c).comp measurable_snd))
  have hg : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        φ (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2))) := fun A c =>
    hφ.comp (hf A c)
  have hfib := Set.indicator_of_mem hS (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2)))
  have hfib' : fibS σ J t m₁ m' s B₀ a κ₁ cm S = _ := hfib
  rw [hfib', lintegral_smul_measure, lintegral_map hφ (hf _ _),
    lintegral_prod _ (hg _ _).aemeasurable, ENNReal.smul_def, smul_eq_mul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

