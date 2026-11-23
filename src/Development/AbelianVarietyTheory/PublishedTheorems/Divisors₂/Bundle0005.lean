module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxF
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.Published

def HeckeFunctionalEquationAbs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (n : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ Λ' : ℂ → ℂ), IsUnitary χ →
      Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) → (∀ v, ExpAt χ v (a v)) → IsCompletedL χ n Λ →
      IsCompletedL χ⁻¹ (fun i => -n i) Λ' → ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ s : ℂ,
        Λ s = ε * ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s)) * Λ' (1 - s)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompleteOfCompactBalls
section
namespace GlobalTheory.L2Kaehler

open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

variable {n : ℕ}

def herm (H : Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → ℂ) : ℝ :=
  (∑ j, ∑ k, H j k * ξ j * (starRingEnd ℂ) (ξ k)).re

def pairBar (v ξ : Fin n → ℂ) : ℂ := ∑ k, v k * (starRingEnd ℂ) (ξ k)

def coNormSq (H : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  (∑ j, ∑ k, H⁻¹ j k * v j * (starRingEnd ℂ) (v k)).re

section Atlas

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def push (A : WeightedAtlas n Y ι La) (i j : ι) (y : Y) (ξ : Fin n → ℂ) : Fin n → ℂ :=
  (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) (WithLp.toLp 2 ξ)).ofLp

structure IsKaehler (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ) :
    Prop where
  smooth : ∀ i j k, ContDiffOn ℝ ∞ (fun v => H i ((A.chart i).symm v) j k) (A.chart i).target
  posDef : ∀ i y, y ∈ (A.chart i).source → (H i y).PosDef
  trans : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → ∀ ξ,
    herm (H i y) ξ = herm (H j y) (push A i j y ξ)
  closed : ∀ i, ∀ v ∈ (A.chart i).target, ∀ j k l,
    wd n l (fun w => H i ((A.chart i).symm w) j k) v =
      wd n j (fun w => H i ((A.chart i).symm w) l k) v

def IsC1Path (A : WeightedAtlas n Y ι La) (γ : ℝ → Y) : Prop :=
  ContinuousOn γ (Set.Icc 0 1) ∧
    ∀ i, ContDiffOn ℝ 1 (A.chart i ∘ γ) (Set.Icc 0 1 ∩ γ ⁻¹' (A.chart i).source)

def pathLength (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (γ : ℝ → Y) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt
    (herm (H (A.pick (γ t)) (γ t)) (deriv (A.chart (A.pick (γ t)) ∘ γ) t).ofLp))

def lengthDist (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (x y : Y) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → Y) (_ : IsC1Path A γ) (_ : γ 0 = x) (_ : γ 1 = y), pathLength A H γ

def IsCauchySeq (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (u : ℕ → Y) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m ≥ N, ∀ k ≥ N, lengthDist A H (u m) (u k) < ε

def IsComplete (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ u : ℕ → Y, IsCauchySeq A H u → ∃ x, MapClusterPt x atTop u

def IsForm (A : WeightedAtlas n Y ι La) (la : La) (v : ι → Y → Fin n → ℂ) : Prop :=
  (∀ i k, ContDiffOn ℝ ∞ (fun w => v i ((A.chart i).symm w) k) (A.chart i).target) ∧
    ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → ∀ ξ,
      pairBar (v i y) ξ = A.g (A.kap + la) i j y * pairBar (v j y) (push A i j y ξ)

def IsDbarClosed (A : WeightedAtlas n Y ι La) (v : ι → Y → Fin n → ℂ) : Prop :=
  ∀ i, ∀ w ∈ (A.chart i).target, ∀ k l,
    wdb n l (fun x => v i ((A.chart i).symm x) k) w = wdb n k (fun x => v i ((A.chart i).symm x) l) w

def dbar (A : WeightedAtlas n Y ι La) (u : ι → Y → ℂ) : ι → Y → Fin n → ℂ :=
  fun i y k => wdb n k (u i ∘ (A.chart i).symm) (A.chart i y)

def formNsq (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ) (la : La)
    (v : ι → Y → Fin n → ℂ) (y : Y) : ℝ :=
  coNormSq (H (A.pick y) y) (v (A.pick y) y) * Real.exp (-A.ph (A.kap + la) (A.pick y) y)

end Atlas

end

end GlobalTheory.L2Kaehler

namespace GlobalTheory.Published

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.L2Kaehler
open scoped ENNReal

def DbarCompleteKaehler : Prop :=
  ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (la : La) (ps : Y → ℝ) (ε : ℝ) (v : ι → Y → Fin n → ℂ),
    IsKaehler A H → IsComplete A H → A.SmoothFn ps → 0 < ε →
    (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      ε * herm (H i y) ξ ≤ A.leviAt i (fun x => A.ph la i x + ps x) y ξ) →
    IsForm A la v → IsDbarClosed A v →
    ∫⁻ y, ENNReal.ofReal (formNsq A H la v y * Real.exp (-ps y)) ∂A.mu < ⊤ →
    ∃ u : ι → Y → ℂ, A.IsSSec (A.kap + la) u ∧
      (∀ i y, y ∈ (A.chart i).source → dbar A u i y = v i y) ∧
      ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) u y * Real.exp (-ps y)) ∂A.mu ≤
        ENNReal.ofReal ε⁻¹ *
          ∫⁻ y, ENNReal.ofReal (formNsq A H la v y * Real.exp (-ps y)) ∂A.mu

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SettingInhabited
section
noncomputable section

open WittVector Ideal CategoryTheory Opposite Function

namespace GlobalTheory.DieudonneTest

open PDivGroup Sandwich Dieudonne

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

open WittVector Ideal CategoryTheory Opposite Function in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
private theorem exists_zmod_mul_of_pow_eq_pow_pred_mul {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} [Fact p.Prime] [CharP R p] {t x : R} (ht : t ≠ 0)
    (hx : x ^ p = t ^ (p - 1) * x) : ∃ k : ZMod p, x = ZMod.castHom (dvd_refl p) R k * t := by
  classical
  by_contra hne
  push_neg at hne
  have hp : p.Prime := Fact.out
  set Q : Polynomial R := Polynomial.X ^ p - Polynomial.C (t ^ (p - 1)) * Polynomial.X with hQ
  have hdeg : Q.natDegree = p := by
    rw [hQ, Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)) hp.one_lt
  have hQ0 : Q ≠ 0 := fun h0 => by
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact hp.ne_zero hdeg.symm
  have hroot : ∀ y, y ^ p = t ^ (p - 1) * y → y ∈ Q.roots := fun y hy => by
    rw [Polynomial.mem_roots hQ0, Polynomial.IsRoot, hQ]
    simp [hy]
  set f : ZMod p → R := fun k => ZMod.castHom (dvd_refl p) R k * t with hf_def
  have hf : Function.Injective f := fun k l hkl =>
    ZMod.castHom_injective R (mul_right_cancel₀ ht hkl)
  have htp : t ^ p = t ^ (p - 1) * t := by rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
  have hfroot : ∀ k, f k ^ p = t ^ (p - 1) * f k := by
    intro k
    simp only [hf_def, mul_pow, ← map_pow, ZMod.pow_card, htp]
    ring
  have hsub : insert x (Finset.univ.image f) ⊆ Q.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hroot _ hx
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
      exact hroot _ (hfroot k)
  have hnot : x ∉ Finset.univ.image f := fun hm => by
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hm
    exact hne k hk.symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hf, Finset.card_univ,
    ZMod.card] at hcard
  have h2 := (Multiset.toFinset_card_le Q.roots).trans (Polynomial.card_roots' Q)
  omega


open WittVector Ideal CategoryTheory Opposite Function in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.DieudonneTest.eigen_step [IsDomain (PreTilt O p)] {ε : PreTilt O p}
    (hε : IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p) {a : _root_.GlobalTheory.Sandwich.Ainf p O}
    (h : WittVector.frobenius a = WittVector.frobenius (_root_.GlobalTheory.Sandwich.xi ε) * a) :
    ∃ (c : ℤ) (b : _root_.GlobalTheory.Sandwich.Ainf p O), a = c * _root_.GlobalTheory.Sandwich.mu ε + p * b ∧
      WittVector.frobenius b = WittVector.frobenius (_root_.GlobalTheory.Sandwich.xi ε) * b := by
  have hp : p.Prime := Fact.out
  have hrp : _root_.GlobalTheory.Sandwich.root ε ^ p = ε := by
    unfold _root_.GlobalTheory.Sandwich.root
    exact frobeniusEquiv_symm_pow_p (PreTilt O p) p ε
  have hε1 : ε ≠ 1 := by
    intro h1
    have hr1 : _root_.GlobalTheory.Sandwich.root ε = 1 := by
      unfold _root_.GlobalTheory.Sandwich.root
      rw [h1, map_one]
    rw [hr1, map_one] at hε
    have h2 := hε.eq_orderOf
    rw [orderOf_one] at h2
    exact hp.one_lt.ne' h2
  set t : PreTilt O p := ε - 1 with ht_def
  have ht : t ≠ 0 := sub_ne_zero.2 hε1
  set s : PreTilt O p := ∑ i ∈ Finset.range p, _root_.GlobalTheory.Sandwich.root ε ^ i with hs
  have hst : s ^ p * t = t ^ p := by
    have h1 : (_root_.GlobalTheory.Sandwich.root ε - 1) * s = t := by rw [hs, mul_geom_sum, hrp]
    have h2 : (_root_.GlobalTheory.Sandwich.root ε - 1) ^ p = t := by rw [sub_pow_char, one_pow, hrp]
    calc s ^ p * t = ((_root_.GlobalTheory.Sandwich.root ε - 1) * s) ^ p := by rw [mul_pow, h2, mul_comm]
      _ = t ^ p := by rw [h1]
  have hsp : s ^ p = t ^ (p - 1) := by
    apply mul_right_cancel₀ ht
    rw [hst, ← pow_succ, Nat.sub_add_cancel hp.one_le]
  have hξ0 : WittVector.coeff (_root_.GlobalTheory.Sandwich.xi ε) 0 = s := by
    rw [← WittVector.constantCoeff_apply]
    unfold _root_.GlobalTheory.Sandwich.xi
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, hs]
  have hμ0 : WittVector.coeff (_root_.GlobalTheory.Sandwich.mu ε) 0 = t := by
    unfold _root_.GlobalTheory.Sandwich.mu
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
  have ha0 : WittVector.coeff a 0 ^ p = t ^ (p - 1) * WittVector.coeff a 0 := by
    have h3 := congrArg (fun x => WittVector.coeff x 0) h
    simp only [WittVector.mul_coeff_zero, WittVector.coeff_frobenius_charP, hξ0] at h3
    rw [h3, hsp]
  obtain ⟨k, hk⟩ := exists_zmod_mul_of_pow_eq_pow_pred_mul ht ha0
  refine ⟨(k.val : ℤ), ?_⟩
  set d : _root_.GlobalTheory.Sandwich.Ainf p O :=
    a - ((k.val : ℤ) : _root_.GlobalTheory.Sandwich.Ainf p O) * _root_.GlobalTheory.Sandwich.mu ε with hd
  have hd0 : WittVector.coeff d 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, hd, map_sub, map_mul, map_intCast,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, hμ0, hk]
    simp
  have hφd : WittVector.frobenius d = WittVector.frobenius (_root_.GlobalTheory.Sandwich.xi ε) * d := by
    rw [hd, map_sub, map_mul, map_intCast, h, _root_.GlobalTheory.Dieudonne.frobenius_mu]
    ring
  have hpd : ∃ b : _root_.GlobalTheory.Sandwich.Ainf p O, d = (p : _root_.GlobalTheory.Sandwich.Ainf p O) * b := by
    by_cases hd00 : d = 0
    · exact ⟨0, by rw [hd00, mul_zero]⟩
    obtain ⟨m, b, hb0, hmb⟩ := WittVector.exists_eq_pow_p_mul d hd00
    cases m with
    | zero =>
      rw [pow_zero, one_mul] at hmb
      rw [hmb] at hd0
      exact absurd hd0 hb0
    | succ m => exact ⟨(p : _root_.GlobalTheory.Sandwich.Ainf p O) ^ m * b, by rw [hmb, pow_succ']; ring⟩
  obtain ⟨b, hb⟩ := hpd
  refine ⟨b, by rw [← hb, hd]; ring, ?_⟩
  have hp0 : (p : _root_.GlobalTheory.Sandwich.Ainf p O) ≠ 0 := WittVector.p_nonzero p _
  apply mul_left_cancel₀ hp0
  have h4 := hφd
  rw [hb, map_mul, map_natCast] at h4
  rw [h4]
  ring

end GlobalTheory.DieudonneTest
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
section
noncomputable section

namespace GlobalTheory.Published

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol
open scoped ENNReal

def TamagawaSpecialUnitary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ))
    [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)]
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E)
    (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)),
    2 ≤ r → Unr E → SelfDualLat G Λ →
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
    (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e →
    IsSReps G (Λ : Set (Fin r → E)) 1 s →
    Multipliable (locFactor E r) ∧
    (∑' j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G)
        (tangentHaar (realSU Ψ G) (formLie Ψ e))) *
      ENNReal.ofReal (|(discr (maximalRealSubfield E) : ℝ)| ^ (-((r : ℝ) ^ 2 - 1) / 2) *
        ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) *
        ∏' v, locFactor E r v) = 1

end GlobalTheory.Published
end
end

