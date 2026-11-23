module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0243
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0242
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0252
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0250

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsUniqueForEpsilonRoot
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

theorem coi_eq_of_mul_eq_zero {R I : Type} [CommRing R] [Fintype I] {e e' : I → R}
    (h : CompleteOrthogonalIdempotents e) (h' : CompleteOrthogonalIdempotents e')
    (hz : ∀ c c', c ≠ c' → e c * e' c' = 0) : e = e' := by
  classical
  funext c
  have h1 : e c = e c * e' c := by
    calc e c = e c * ∑ b, e' b := by rw [h'.complete, mul_one]
      _ = e c * e' c := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_single c (fun b _ hb => hz c b hb.symm) (by simp)
  have h2 : e' c = e c * e' c := by
    calc e' c = (∑ b, e b) * e' c := by rw [h.complete, one_mul]
      _ = e c * e' c := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_single c (fun b _ hb => hz b c hb) (by simp)
  rw [h1, ← h2]

theorem one_sub_pow_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {n d : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (hd : 0 < d) (hdn : d < n) : 1 - ζ ^ d ∣ (n : O) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := hζ.prod_one_sub_pow_eq_order
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  have hd' : (1 - ζ ^ (j + 1)) ∣ ∏ i ∈ Finset.range k, (1 - ζ ^ (i + 1)) :=
    Finset.dvd_prod_of_mem (fun i => 1 - ζ ^ (i + 1)) (Finset.mem_range.2 (by omega))
  rw [h] at hd'
  simpa using hd'

theorem pow_sub_pow_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {n a b : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    ζ ^ a - ζ ^ b ∣ (n : O) := by
  have hu : ∀ i : ℕ, IsUnit (ζ ^ i) := fun i =>
    (hζ.isUnit (by omega)).pow i
  have key : ∀ {a b : ℕ}, a < b → b < n → ζ ^ a - ζ ^ b ∣ (n : O) := by
    intro a b h1 h2
    have e : ζ ^ a - ζ ^ b = ζ ^ a * (1 - ζ ^ (b - a)) := by
      rw [mul_sub, mul_one, ← pow_add]
      congr 2
      omega
    rw [e]
    exact (hu a).mul_left_dvd.2 (one_sub_pow_dvd hζ (by omega) (by omega))
  rcases lt_or_gt_of_ne hab with h | h
  · exact key h hb
  · rw [← neg_sub, neg_dvd]
    exact key h ha

theorem mul_eq_zero_of_pow {O U : Type} [CommRing O] [IsDomain O] [CommRing U] (g : O →+* U)
    {ζ : O} {n a b : ℕ} (hζ : IsPrimitiveRoot ζ n) (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (hn : (n : U) ∈ nonZeroDivisors U) {x S S' : U}
    (h : S * (x - g ζ ^ a) = 0) (h' : S' * (x - g ζ ^ b) = 0) : S * S' = 0 := by
  obtain ⟨w, hw⟩ := pow_sub_pow_dvd hζ ha hb hab
  have e : (n : U) = (g ζ ^ a - g ζ ^ b) * g w := by
    rw [← map_natCast g, hw, map_mul, map_sub, map_pow, map_pow]
  have h0 : S * S' * (g ζ ^ a - g ζ ^ b) = 0 := by
    linear_combination S * h' * 1 - S' * h
  have h1 : (S * S') * (n : U) = 0 := by
    rw [e, ← mul_assoc, h0, zero_mul]
  exact (mem_nonZeroDivisors_iff_right.1 hn) _ h1

variable {l : ℕ} [Fact l.Prime]

theorem sharp_s_eq (t : PAlg l) (x : Ob l) :
    t.sharp (t.s x) = t.oC (theta0 l (WittVector.teichmuller l x)) := by
  rw [oC_theta0, sW, WittVector.map_teichmuller]
  rfl

theorem eq_zero_of_sharp (t : PAlg l) {e : t.A} (he : IsIdempotentElem e) (h : t.sharp e = 0) :
    e = 0 :=
  (RL.idem_au t 0 IsIdempotentElem.zero).unique ⟨he, h⟩ ⟨IsIdempotentElem.zero, sharp_zero t⟩

theorem idem_unique : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l) (m : ℕ) (x : t.U)
    (e e' : ZMod (l ^ m) → t.A),
    CompleteOrthogonalIdempotents e → CompleteOrthogonalIdempotents e' →
    (∀ c, t.sharp (e c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) →
    (∀ c, t.sharp (e' c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) → e = e' := by
  intro l _ ε t m x e e' he he' h h'
  have hζ := (GlobalTheory.T.epsilon_cyclotomic_element_properties ε).2.2.2.2 m
  refine coi_eq_of_mul_eq_zero he he' fun c c' hc => ?_
  have hn : ((l ^ m : ℕ) : t.U) ∈ nonZeroDivisors t.U := by
    rw [Nat.cast_pow]
    exact pow_mem t.l_mem_nzd_U m
  have h1 := h c
  have h2 := h' c'
  rw [sharp_s_eq] at h1 h2
  have h3 := mul_eq_zero_of_pow t.oC hζ (ZMod.val_lt c) (ZMod.val_lt c')
    (fun hv => hc (ZMod.val_injective _ hv)) hn h1 h2
  refine eq_zero_of_sharp t ((he.idem c).mul (he'.idem c')) ?_
  rw [map_mul, h3]

end GlobalTheory.CompanionTheory.ContUniv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InclRedM
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedPull

theorem incl_redM : ∀ {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r : Option ℤ) (c : b.R) (j : ℕ) (z : HO Q j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r c)).pull j (redM Q r c j z) =
      redM Q' r c j ((incl h).o.pull j z) := by
  intro b L Q Q' h r c j z
  exact sq_toSq (incl h) _ _ (fun _ _ _ => trivial) (incl_std h r c) j z

end GlobalTheory.CompanionTheory.RedPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatSFiniteSpan
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem latS_finite_span {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] K'] :
    ∃ T : Finset (Formalism.Per6.BdRp l), (∀ t ∈ T, t ∈ latS K') ∧
      ∀ s ∈ latS K', ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t) := by
  have hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K') :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K' (integralClosure ℤ_[l] K')
  have htow : IsScalarTower ℤ_[l] K' (Om l) := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K']
    rfl)
  obtain ⟨b₀, hb₀⟩ := hfin.fg_top
  let ι : ↥(integralClosure ℤ_[l] K') → Formalism.Per6.BdRp l := fun b => rB l ((b : K') : Om l)
  let _ : Algebra (Wl l) (Formalism.Per6.BdRp l) := (wB l).toAlgebra
  have hsm : ∀ (a : Wl l) (x : Formalism.Per6.BdRp l), a • x = wB l a * x := fun a x => Algebra.smul_def a x
  let T : Finset (Formalism.Per6.BdRp l) := b₀.image ι
  let N : Submodule (Wl l) (Formalism.Per6.BdRp l) := Submodule.span (Wl l) (T : Set (Formalism.Per6.BdRp l))
  have hZ : ∀ c : ℤ_[l], rB l (algebraMap ℤ_[l] (Om l) c) =
      wB l (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l c) := by
    intro c
    have h := GroundTheory.PAdicHodge.IsPerfectoidField.algebraMap_padic_coe (K := ℂ_[l]) l c
    have h2 := (GroundTheory.PAdicHodge.algClToBdR l).commutes (c : ℚ_[l])
    exact h2.trans h
  have hιmul : ∀ x y, ι (x * y) = ι x * ι y := fun x y => by simp [ι]
  have hO : ∀ z, ι z ∈ N := by
    intro z
    have hz : z ∈ Submodule.span ℤ_[l] (b₀ : Set ↥(integralClosure ℤ_[l] K')) := hb₀ ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))
    | zero => simp [ι]
    | add x y _ _ hx hy =>
      have e : ι (x + y) = ι x + ι y := by simp [ι]
      rw [e]; exact N.add_mem hx hy
    | smul c x _ hx =>
      have e : ι (c • x) = (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l c) • ι x := by
        rw [hsm, ← hZ]
        have e2 : (((c • x : ↥(integralClosure ℤ_[l] K')) : K') : Om l) =
            algebraMap ℤ_[l] (Om l) c * ((x : K') : Om l) := by
          have : ((c • x : ↥(integralClosure ℤ_[l] K')) : K') = c • (x : K') := rfl
          rw [this, Algebra.smul_def, IntermediateField.coe_mul]
          exact congrArg (· * ((x : K') : Om l)) (IsScalarTower.algebraMap_apply ℤ_[l] K' (Om l) c).symm
        simp only [ι, e2, map_mul]
      rw [e]; exact N.smul_mem _ hx
  have hmul : N * N ≤ N := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b', _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    change ι b * ι b' ∈ N
    rw [← hιmul]
    exact hO _
  have h1 : (1 : Formalism.Per6.BdRp l) ∈ N := by
    have := hO 1
    simpa [ι] using this
  have hint : ∀ b : ↥(integralClosure ℤ_[l] K'), IsIntegral ℤ_[l] ((b : K') : Om l) := fun b =>
    (isIntegral_algebraMap_iff (A := K') (B := Om l) ).2 b.2
  have hS : ∀ x ∈ latS K', x ∈ N := by
    intro x hx
    unfold latS at hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨y, ⟨hyK, hyI⟩, rfl⟩
      · have := N.smul_mem a h1
        rwa [hsm, mul_one] at this
      · have hz : IsIntegral ℤ_[l] (⟨y, hyK⟩ : K') :=
          (isIntegral_algebraMap_iff (A := K') (B := Om l) ).1 hyI
        exact hO ⟨⟨y, hyK⟩, hz⟩
    | zero => exact N.zero_mem
    | one => exact h1
    | add _ _ _ _ hx hy => exact N.add_mem hx hy
    | neg _ _ hx => exact N.neg_mem hx
    | mul _ _ _ _ hx hy => exact hmul (Submodule.mul_mem_mul hx hy)
  refine ⟨T, ?_, ?_⟩
  · intro t ht
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 ht
    exact rB_mem_latS K' (b : K').2 (hint b)
  · intro x hx
    obtain ⟨f, _, hf⟩ := Submodule.mem_span_finset.1 (hS x hx)
    exact ⟨f, by rw [← hf]; exact Finset.sum_congr rfl (fun t _ => by rw [hsm, mul_comm])⟩

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSeriesDeRhamPeriod
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Glue

section Abs

variable {B : Type} [CommRing B]

def InMul (S : Subring B) (ϖ z : B) : Prop := ∃ s ∈ S, z = ϖ * s

theorem InMul.add {S : Subring B} {ϖ z w : B} (hz : InMul S ϖ z) (hw : InMul S ϖ w) :
    InMul S ϖ (z + w) := by
  obtain ⟨s, hs, rfl⟩ := hz
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨s + t, S.add_mem hs ht, by ring⟩

theorem InMul.sub {S : Subring B} {ϖ z w : B} (hz : InMul S ϖ z) (hw : InMul S ϖ w) :
    InMul S ϖ (z - w) := by
  obtain ⟨s, hs, rfl⟩ := hz
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨s - t, S.sub_mem hs ht, by ring⟩

theorem InMul.mul {S : Subring B} {ϖ z w : B} (hz : InMul S ϖ z) (hw : w ∈ S) :
    InMul S ϖ (z * w) := by
  obtain ⟨s, hs, rfl⟩ := hz
  exact ⟨s * w, S.mul_mem hs hw, by ring⟩

theorem inMul_zero (S : Subring B) (ϖ : B) : InMul S ϖ 0 :=
  ⟨0, S.zero_mem, by ring⟩

theorem pow_sub_pow_inMul {S : Subring B} {ϖ T f s : B} (hϖ : ϖ ∈ S) (hT : T ∈ S) (hs : s ∈ S)
    (h : T = ϖ * s + f) (k : ℕ) : InMul S ϖ (T ^ k - f ^ k) := by
  have hf : f ∈ S := by
    have : f = T - ϖ * s := by rw [h]; ring
    rw [this]
    exact S.sub_mem hT (S.mul_mem hϖ hs)
  induction k with
  | zero => simpa using inMul_zero S ϖ
  | succ k ih =>
    have e : T ^ (k + 1) - f ^ (k + 1) = (T ^ k - f ^ k) * T + (ϖ * s) * f ^ k := by
      rw [pow_succ, pow_succ]
      have : f ^ k * f = f ^ k * (T - ϖ * s) := by rw [h]; ring
      rw [this]; ring
    rw [e]
    exact (ih.mul hT).add ⟨s * f ^ k, S.mul_mem hs (S.pow_mem hf k), by ring⟩

theorem evalMod_of_lift {R T : Type} [CommRing R] [CommRing T] (S : Subring B) (F : ℕ → Ideal B)
    (ϖ : B) (h : R →+* B) (τ : T →* B) (r : R →+* T) (hτ0 : τ 0 = 0) (hτS : ∀ a, τ a ∈ S)
    (hϖ : ϖ ∈ S) (hadd : ∀ a b, InMul S ϖ (τ (a + b) - τ a - τ b))
    (hcoef : ∀ c, InMul S ϖ (h c - τ (r c))) (hF : ∀ k, ∀ f ∈ F 1, f ^ k ∈ F k)
    (x y : T) (φ : PowerSeries R)
    (hy : ∀ D, x ^ D ∣ y - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i)
    (M : ℕ) (s : B) (hs : s ∈ S) (hM : τ x ^ M - ϖ * s ∈ F 1) (k : ℕ) :
    ∃ D, ∀ D' ≥ D, Near S ϖ (F k) 1
      ((∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * τ x ^ i) - τ y) := by
  have hsum : ∀ D, InMul S ϖ ((∑ i ∈ Finset.range D, h (PowerSeries.coeff i φ) * τ x ^ i) -
      τ (∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i)) := by
    intro D
    induction D with
    | zero => simpa [hτ0] using inMul_zero S ϖ
    | succ D ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      generalize hA : (∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i) = A at ih ⊢
      generalize hP : (∑ i ∈ Finset.range D, h (PowerSeries.coeff i φ) * τ x ^ i) = P at ih ⊢
      have e1 : P + h (PowerSeries.coeff D φ) * τ x ^ D -
          τ (A + r (PowerSeries.coeff D φ) * x ^ D) =
          (P - τ A) + (h (PowerSeries.coeff D φ) - τ (r (PowerSeries.coeff D φ))) * τ x ^ D -
          (τ (A + r (PowerSeries.coeff D φ) * x ^ D) - τ A -
            τ (r (PowerSeries.coeff D φ) * x ^ D)) := by
        rw [map_mul τ, map_pow τ]; ring
      rw [e1]
      exact (ih.add ((hcoef _).mul (S.pow_mem (hτS x) D))).sub (hadd _ _)
  refine ⟨M * k, fun D' hD' => ?_⟩
  obtain ⟨b, hb⟩ := hy D'
  have hP := hsum D'
  generalize (∑ i ∈ Finset.range D', r (PowerSeries.coeff i φ) * x ^ i) = A at hb hP
  generalize (∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * τ x ^ i) = P at hP ⊢
  have hyA : y = A + x ^ D' * b := by rw [← hb]; ring
  obtain ⟨a, ha, hT⟩ := pow_sub_pow_inMul hϖ (S.pow_mem (hτS x) M) hs
    (f := τ x ^ M - ϖ * s) (by ring) k
  obtain ⟨u, hu, hPu⟩ := hP
  obtain ⟨v, hv, hv'⟩ := hadd A (x ^ D' * b)
  have hg : (τ x ^ M - ϖ * s) ^ k ∈ F k := hF k _ hM
  set g := (τ x ^ M - ϖ * s) ^ k with hgdef
  have hpow : τ x ^ D' = (τ x ^ M) ^ k * τ x ^ (D' - M * k) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hw : τ x ^ (D' - M * k) * τ b ∈ S := S.mul_mem (S.pow_mem (hτS x) _) (hτS b)
  obtain ⟨w, hwdef⟩ : ∃ w, w = τ x ^ (D' - M * k) * τ b := ⟨_, rfl⟩
  rw [← hwdef] at hw
  have hC : τ (x ^ D' * b) = (τ x ^ M) ^ k * w := by
    rw [map_mul τ, map_pow τ, hpow, hwdef]; ring
  refine ⟨u - v - a * w, S.sub_mem (S.sub_mem hu hv) (S.mul_mem ha hw), ?_⟩
  have e : P - τ y - ϖ ^ 1 * (u - v - a * w) = -(g * w) := by
    rw [hyA]
    linear_combination hPu - hv' - hC - w * hT
  rw [e]
  exact (F k).neg_mem (Ideal.mul_mem_right w (F k) hg)

end Abs

section Conc

variable (l : ℕ) [Fact l.Prime]

def tchHom : Tl l →* Formalism.Per6.BdRp l :=
  ((wB l : Wl l →+* Formalism.Per6.BdRp l) : Wl l →* Formalism.Per6.BdRp l).comp (WittVector.teichmuller l)

theorem tchHom_apply (a : Tl l) : tchHom l a = tch l a := rfl

theorem tchHom_zero : tchHom l 0 = 0 := by
  simp [tchHom]

theorem teichmuller_add_sub (a b : Tl l) : ∃ w : Wl l,
    WittVector.teichmuller l (a + b) - WittVector.teichmuller l a - WittVector.teichmuller l b
      = w * (l : Wl l) := by
  set z : Wl l := WittVector.teichmuller l (a + b) - WittVector.teichmuller l a -
    WittVector.teichmuller l b with hz
  have h0 : z.coeff 0 = 0 := by
    have : WittVector.constantCoeff z = 0 := by
      simp [hz, map_sub]
    simpa using this
  have h1 : z = WittVector.verschiebung (z.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (n := 1) (x := z) (by
      intro i hi
      obtain rfl : i = 0 := by omega
      exact h0)
    simpa using this
  obtain ⟨u, hu⟩ := (WittVector.frobenius_bijective l (Tl l)).2 (z.shift 1)
  refine ⟨u, ?_⟩
  rw [h1, ← hu, WittVector.verschiebung_frobenius]

end Conc

theorem evalMod_teichmuller : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (π : ↥(OL K)) (S : Subring (Formalism.Per6.BdRp l)),
    (∀ a, wB l a ∈ S) → (∀ c, oB K μ c ∈ S) → PerEnv S (FB l) (oB K μ π) → π ∣ (l : ↥(OL K)) →
    ∀ (r : ↥(OL K) →+* Tl l), (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) →
    ∀ (x y : Tl l), ‖thB l (tch l x)‖ < 1 → ∀ (φ : PowerSeries ↥(OL K)),
      (∀ D, x ^ D ∣ y - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i) →
      EvalMod S (FB l) (oB K μ π) (oB K μ) φ (tch l x) (tch l y) 1 := by
  intro l _ K μ π S hw ho env hπ r hr x y hx φ hy k
  obtain ⟨e, he⟩ := hπ
  have hl : ((l : ℕ) : Formalism.Per6.BdRp l) = oB K μ π * oB K μ e := by
    rw [← map_mul, ← he, map_natCast]
  have hadd : ∀ a b, InMul S (oB K μ π) (tchHom l (a + b) - tchHom l a - tchHom l b) := by
    intro a b
    obtain ⟨w, hw'⟩ := teichmuller_add_sub l a b
    refine ⟨wB l w * oB K μ e, S.mul_mem (hw _) (ho _), ?_⟩
    have := congrArg (wB l) hw'
    simp only [map_sub, map_mul, map_natCast] at this
    simp only [tchHom_apply, tch]
    rw [this, hl]; ring
  have hcoef : ∀ c, InMul S (oB K μ π) (oB K μ c - tchHom l (r c)) := by
    intro c
    obtain ⟨c', hc'⟩ := hr c
    refine ⟨- oB K μ c', S.neg_mem (ho _), ?_⟩
    rw [tchHom_apply, hc', map_add (f := _), map_mul]; ring
  have hϖ0 : thB l (oB K μ π) ≠ 0 := (env.unit.map (thB l)).ne_zero
  obtain ⟨M, -, s, hs, hM⟩ := _root_.GlobalTheory.CompanionTheory.LTPer.TopNil.main S hw (oB K μ π) hϖ0 x hx
  rw [pow_one] at hM
  exact evalMod_of_lift S (FB l) (oB K μ π) (oB K μ) (tchHom l) r (tchHom_zero l)
    (fun a => hw _) env.mem hadd hcoef
    (fun k f hf => Ideal.pow_mem_pow (by simpa [FB] using hf) k) x y φ hy M s hs hM k

end GlobalTheory.CompanionTheory.LTPer.Glue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonemptyOpenIdealNotNilpotent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.NonIso

theorem exists_ideal_not_pow_le {X : Scheme.{0}} (J : X.IdealSheafData) (W : J.subscheme.Opens)
    (hW : (W : Set J.subscheme).Nonempty) :
    ∃ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V →
      J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W) ∧ ∀ m, ¬ powIdeal J₀ m ≤ J := by
  have hC : IsClosed (J.subschemeι '' (W : Set J.subscheme)ᶜ) :=
    J.subschemeι.isClosedEmbedding.isClosedMap _ W.isOpen.isClosed_compl
  let C : TopologicalSpace.Closeds X := ⟨_, hC⟩
  have hsupp : ∀ x : X, x ∈ (Scheme.IdealSheafData.vanishingIdeal C).support ↔
      x ∈ J.subschemeι '' (W : Set J.subscheme)ᶜ := by
    intro x
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  refine ⟨Scheme.IdealSheafData.vanishingIdeal C, ?_, ?_⟩
  · intro V f hf y hy
    have hyV : J.subschemeι y ∈ (V : X.Opens) := X.basicOpen_le f hy
    by_contra hyW
    have h1 : J.subschemeι y ∈ (Scheme.IdealSheafData.vanishingIdeal C).support :=
      (hsupp _).2 ⟨y, hyW, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyV, Scheme.mem_zeroLocus_iff] at h1
    exact h1 f hf hy
  · intro m hm
    obtain ⟨w, hw⟩ := hW
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
      (show J.subschemeι w ∈ (⊤ : X.Opens) from trivial)
    let V' : X.affineOpens := ⟨V, hV⟩
    have hxV' : J.subschemeι w ∈ (V' : X.Opens) := hxV
    have hnC : J.subschemeι w ∉ (Scheme.IdealSheafData.vanishingIdeal C).support := by
      rw [hsupp]
      rintro ⟨w', hw', he⟩
      exact hw' (J.subschemeι.isClosedEmbedding.injective he ▸ hw)
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV', Scheme.mem_zeroLocus_iff] at hnC
    push_neg at hnC
    obtain ⟨f, hf, hxf⟩ := hnC
    have hfm : f ^ m ∈ J.ideal V' := Scheme.IdealSheafData.le_def.1 hm V' (Ideal.pow_mem_pow hf m)
    have hxJ : J.subschemeι w ∈ J.support := by
      rw [← SetLike.mem_coe, ← J.range_subschemeι]; exact ⟨w, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV', Scheme.mem_zeroLocus_iff] at hxJ
    refine hxJ (f ^ m) hfm ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    · rwa [Scheme.basicOpen_pow _ _ hm0]

end GlobalTheory.CompanionTheory.GE.NonIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResKOne
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SiteCup

variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem resK_cup (Q : ObjectProperty (Thick (smFun X q))) {i j k : ℕ} (h : i + j = k) (x : HdR q i) (y : HdR q j) :
    resK q Q k (cupK q h x y) = (CH.mulP (sP Q).A).cup h (resK q Q i x) (resK q Q j y) :=
  CrystallineSemistableComparison.P.cup_pull (CH.mulP (thA (smFun X q))) (CH.mulP (sP Q).A) Q.ι
    (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).τ (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).τ
    (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).τ (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).nat
    (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).nat (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).nat
    (fun _ _ _ => rfl) h x y

theorem resK_one (Q : ObjectProperty (Thick (smFun X q))) : resK q Q 0 (oneK q) = CH.oneH (sP Q).A :=
  pull_unit_class (thA (smFun X q)) (sP Q).A (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι) fun _ => rfl

theorem muB_cup : ∀ {K B' : Type} [CommRing K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (l s : ℕ) (𝒱 : Set X.Opens), (∀ {i j k : ℕ} (h : i + j = k) (x : HdR q i) (y : HdR q j),
      muB γ q l s 𝒱 k (cupK q h x y) = (CH.mulP (sP (TS γ q l s 𝒱)).A).cup h (muB γ q l s 𝒱 i x) (muB γ q l s 𝒱 j y)) ∧
    muB γ q l s 𝒱 0 (oneK q) = CH.oneH (sP (TS γ q l s 𝒱)).A := by
  intro K B' _ _ _ I γ X q l s 𝒱
  refine ⟨fun {i j k} h x y => ?_, ?_⟩
  · change (smO γ q l s 𝒱).o.pull k (resK q (TO q l s 𝒱) k (cupK q h x y)) =
      (CH.mulP (sP (TS γ q l s 𝒱)).A).cup h ((smO γ q l s 𝒱).o.pull i (resK q (TO q l s 𝒱) i x))
        ((smO γ q l s 𝒱).o.pull j (resK q (TO q l s 𝒱) j y))
    rw [resK_cup]
    exact (smor_cup (smO γ q l s 𝒱)).1 h _ _
  · change (smO γ q l s 𝒱).o.pull 0 (resK q (TO q l s 𝒱) 0 (oneK q)) = _
    rw [resK_one]
    exact (smor_cup (smO γ q l s 𝒱)).2

end GlobalTheory.CompanionTheory.SiteCup
end

