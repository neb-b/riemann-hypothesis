module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.PlaceInt

theorem host_bar_eq_smul (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (x : 𝓞 D.host.E) :
    H.bar x = D.host.conj • x := by
  apply RingOfIntegers.ext
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact (D.host.conjE_apply φ x).symm

theorem host_galois_discr_moves : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), IsGalois ℚ D.host.E ∧ Module.finrank ℚ D.host.E = 4 * D.R.ord ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr D.host.E → p ∣ D.host.condN) ∧ ∀ p ∈ D.host.condN.primeFactors, p.Prime ∧ ∀ 𝔭 : Ideal (𝓞 D.host.E), 𝔭.IsPrime → (p : 𝓞 D.host.E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭 := by
  intro D H
  refine ⟨D.host.galois, D.host.der.finrank_E, D.host.der.discr_primes.1, ?_⟩
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, fun P hP hmem => ?_⟩
    by_contra hall
    push Not at hall
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hpp).irreducible
    have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := by
      refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 D.host.E) (p : ℤ) ∈ P
      rw [map_natCast]
      exact hmem
    have hbb : ∀ x : 𝓞 D.host.E, H.bar (H.bar x) = x := fun x => by
      apply RingOfIntegers.ext
      rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
    refine D.host.der.decompConj p hpp (Nat.dvd_of_mem_primeFactors hp) P ?_
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (D.host.conj)⁻¹ • x = H.bar x := by
      rw [inv_smul_eq_iff, ← host_bar_eq_smul D H, hbb]
    rw [hinv]
    refine ⟨fun h => ?_, hall x⟩
    have := hall _ h
    rwa [hbb] at this

end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InZhIffKillsAdapted
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.ZPart

section Mod
variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] {n : ℕ}

def Kl (mu : Matrix (Fin n) (Fin n) O) (u : Fin n → M) : Prop := ∀ i, ∑ j, mu i j • u j = 0

theorem Kl.mul {b : Matrix (Fin n) (Fin n) O} {u : Fin n → M} (h : Kl b u) (a : Matrix (Fin n) (Fin n) O) :
    Kl (a * b) u := by
  intro i
  simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, h _, smul_zero, Finset.sum_const_zero]

theorem Kl.smul {b : Matrix (Fin n) (Fin n) O} {u : Fin n → M} (h : Kl b u) (a : O) : Kl (a • b) u := by
  intro i
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, h i, smul_zero]

theorem Kl.cancel {b : Matrix (Fin n) (Fin n) O} {u : Fin n → M} {a ℓ : O} (hc : IsCoprime a ℓ)
    (hu : ∀ j, ∃ e : ℕ, ℓ ^ e • u j = 0) (h : Kl (a • b) u) : Kl b u := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ j, ℓ ^ e • u j = 0 := by
    choose f hf using hu
    refine ⟨∑ j, f j, fun j => ?_⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (fun x _ => Nat.zero_le (f x)) (Finset.mem_univ j))
    rw [hd, pow_add, mul_comm, mul_smul, hf j, smul_zero]
  intro i
  obtain ⟨x, y, hxy⟩ := hc.pow_right (n := e)
  have h1 : a • ∑ j, b i j • u j = 0 := by
    rw [Finset.smul_sum]
    simpa only [Matrix.smul_apply, smul_eq_mul, mul_smul] using h i
  have h2 : ℓ ^ e • ∑ j, b i j • u j = 0 := by
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_smul, mul_comm, mul_smul, he j, smul_zero]
  calc ∑ j, b i j • u j = (x * a + y * ℓ ^ e) • ∑ j, b i j • u j := by rw [hxy, one_smul]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, h1, h2, smul_zero, smul_zero, add_zero]
end Mod

section Lat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {Λ : GenLat E n} {N ℓ : ℕ} (A : Adapt Λ N ℓ)

noncomputable def adj : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => IsCMField.complexConj E (A.ga j i)

theorem adj_mul : adj A * A.ga = 1 := by
  ext i j
  simp only [adj, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  exact A.unitary i j

theorem map_inj {a b : Matrix (Fin n) (Fin n) (𝓞 E)}
    (h : a.map (algebraMap (𝓞 E) E) = b.map (algebraMap (𝓞 E) E)) : a = b := by
  refine Matrix.ext fun i j => ?_
  have h' := congrArg (fun m : Matrix (Fin n) (Fin n) E => m i j) h
  simp only [Matrix.map_apply] at h'
  exact FaithfulSMul.algebraMap_injective (𝓞 E) E h'

theorem exists_adj : ∃ r : Matrix (Fin n) (Fin n) (𝓞 E),
    r * (A.p * A.q) = ((A.k ^ 2 : ℕ) : 𝓞 E) • ((N ^ 2 : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) := by
  let σ : 𝓞 E →+* 𝓞 E := NumberField.RingOfIntegers.mapRingHom (IsCMField.complexConj E).toRingHom
  refine ⟨Matrix.of fun i j => σ ((A.p * A.q) j i), map_inj ?_⟩
  have hr : (Matrix.of fun i j => σ ((A.p * A.q) j i)).map (algebraMap (𝓞 E) E) =
      ((A.k * N : ℕ) : E) • adj A := by
    ext i j
    have hji := congrArg (fun m : Matrix (Fin n) (Fin n) E => m j i) A.prod
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hji
    have hσ : algebraMap (𝓞 E) E (σ ((A.p * A.q) j i)) =
        IsCMField.complexConj E (algebraMap (𝓞 E) E ((A.p * A.q) j i)) := rfl
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, adj, hσ, hji, map_mul,
      map_natCast]
  rw [Matrix.map_mul, hr, A.prod, Matrix.smul_mul, Matrix.mul_smul, adj_mul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem exists_factor (mu : Matrix (Fin n) (Fin n) E) (hmu : ∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) (c : ℕ)
    (cm : Matrix (Fin n) (Fin n) (𝓞 E)) (hcm : ∀ i j, (cm i j : E) = ((c * N : ℕ) : E) * mu i j) :
    ∃ r : Matrix (Fin n) (Fin n) (𝓞 E), r * (A.p * A.q) = ((A.k ^ 2 : ℕ) : 𝓞 E) • cm := by
  have hW : ∀ j : Fin n, ∃ w ∈ Λ.La, (A.k : E) • (Pi.single j 1 : Fin n → E) = A.ga.mulVec w := by
    intro j
    refine A.onto _ ?_
    simp only [stdLat, Submodule.mem_pi]
    intro i _
    refine Submodule.mem_one.mpr ⟨(Pi.single j (1 : 𝓞 E) : Fin n → 𝓞 E) i, ?_⟩
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  choose w hwΛ hw using hW
  have hy : ∀ i j, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = mu.mulVec (w j) i := by
    intro i j
    have hm := hmu _ (hwΛ j)
    simp only [stdLat, Submodule.mem_pi] at hm
    exact Submodule.mem_one.mp (hm i (Set.mem_univ i))
  choose y hy using hy
  refine ⟨Matrix.of fun i j => (c : 𝓞 E) * y i j, map_inj ?_⟩
  have hGW : A.ga * Matrix.of (fun b j => w j b) = (A.k : E) • (1 : Matrix (Fin n) (Fin n) E) := by
    ext b j
    have hb := congrFun (hw j) b
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at hb
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [← hb]
  have hWadj : Matrix.of (fun b j => w j b) = (A.k : E) • adj A := by
    calc Matrix.of (fun b j => w j b) = adj A * A.ga * Matrix.of (fun b j => w j b) := by
          rw [adj_mul, Matrix.one_mul]
      _ = (A.k : E) • adj A := by rw [Matrix.mul_assoc, hGW, Matrix.mul_smul, Matrix.mul_one]
  have hr : (Matrix.of fun i j => (c : 𝓞 E) * y i j).map (algebraMap (𝓞 E) E) =
      (c : E) • (mu * Matrix.of (fun b j => w j b)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_natCast, hy, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [Matrix.map_mul, hr, A.prod, hWadj]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, adj_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, hcm]
  push_cast
  ring
end Lat

section Pts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (T : Over Xo.X)

@[reducible] noncomputable def ptMod : Module (𝓞 E) (Additive (T ⟶ Xo.univ.t.G)) where
  smul a x := Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act a)
  one_smul x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act 1) = x
    rw [Xo.univ.t.act.one, Category.comp_id]; rfl
  mul_smul a b x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act (a * b)) =
      Additive.ofMul ((x.toMul ≫ Xo.univ.t.act.act b) ≫ Xo.univ.t.act.act a)
    rw [_root_.mul_comm, Xo.univ.t.act.mul, Category.assoc]
  smul_zero a := by
    have := Xo.univ.t.act.hom a
    exact congrArg Additive.ofMul (MonObj.one_comp (Xo.univ.t.act.act a))
  smul_add a x y := by
    have := Xo.univ.t.act.hom a
    exact congrArg Additive.ofMul (MonObj.mul_comp x.toMul y.toMul (Xo.univ.t.act.act a))
  add_smul a b x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act (a + b)) = _
    rw [Xo.univ.t.act.add, MonObj.comp_mul]; rfl
  zero_smul x := by
    change Additive.ofMul (x.toMul ≫ Xo.univ.t.act.act 0) = _
    have h := ZhStable.act_natCast Xo 0
    rw [Nat.cast_zero, pow_zero] at h
    rw [h, MonObj.comp_one]; rfl

variable {T}

theorem kills_iff {n : ℕ} (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (u : Fin n → (T ⟶ Xo.univ.t.G)) :
    letI := ptMod Xo T
    Kills Xo mu u ↔ Kl mu (fun j => Additive.ofMul (u j)) := by
  refine forall_congr' fun i => ?_
  change (List.ofFn fun j => u j ≫ Xo.univ.t.act.act (mu i j)).prod = 1 ↔
    ∑ j, Additive.ofMul (u j ≫ Xo.univ.t.act.act (mu i j)) = 0
  rw [List.prod_ofFn, ← ofMul_prod, ofMul_eq_zero]

theorem pow_iff (m : ℕ) (x : T ⟶ Xo.univ.t.G) :
    letI := ptMod Xo T
    x ^ m = 1 ↔ (m : 𝓞 E) • Additive.ofMul x = 0 := by
  change x ^ m = 1 ↔ Additive.ofMul (x ≫ Xo.univ.t.act.act (m : 𝓞 E)) = 0
  rw [ZhStable.act_natCast Xo m, MonObj.comp_pow, Category.comp_id, ofMul_eq_zero]

theorem inZh_iff {n : ℕ} {Λ : GenLat E n} {N ℓ : ℕ} (A : Adapt Λ N ℓ) (u : Fin n → (T ⟶ Xo.univ.t.G))
    (hu : ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1) (c : ℕ) (hc : Nat.Coprime c ℓ) :
    InZh Xo Λ (c * N) u ↔ Kills Xo (A.p * A.q) u := by
  letI := ptMod Xo T
  have tors : ∀ j, ∃ e : ℕ, (ℓ : 𝓞 E) ^ e • Additive.ofMul (u j) = 0 := by
    intro j
    obtain ⟨e, he⟩ := hu j
    have h := (pow_iff Xo (ℓ ^ e) (u j)).mp he
    rw [Nat.cast_pow] at h
    exact ⟨e, h⟩
  have cop : ∀ m : ℕ, Nat.Coprime m ℓ → IsCoprime (m : 𝓞 E) (ℓ : 𝓞 E) := by
    intro m hm
    simpa using (Nat.isCoprime_iff_coprime.mpr hm).map (Int.castRingHom (𝓞 E))
  constructor
  · rintro ⟨-, hZ⟩
    have hK : Kills Xo ((c : 𝓞 E) • (A.p * A.q)) u := by
      refine hZ ((A.k : E) • A.ga) (fun v hv => ?_) _ (fun i j => ?_)
      · rw [Matrix.smul_mulVec]
        exact A.into v hv
      · have hij := congrArg (fun m : Matrix (Fin n) (Fin n) E => m i j) A.prod
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hij
        change algebraMap (𝓞 E) E ((c : 𝓞 E) * (A.p * A.q) i j) = _
        rw [map_mul, map_natCast, hij, Matrix.smul_apply, smul_eq_mul]
        push_cast
        ring
    exact (kills_iff Xo _ u).mpr (((kills_iff Xo _ u).mp hK).cancel (cop c hc) tors)
  · intro hK
    have hKl := (kills_iff Xo _ u).mp hK
    refine ⟨fun b => ?_, fun mu hmu cm hcm => ?_⟩
    · obtain ⟨r, hr⟩ := exists_adj A
      have h1 := hKl.mul r
      rw [hr] at h1
      have h2 := (h1.cancel (cop _ (A.cop.pow_left 2)) tors) b
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one, mul_zero, ite_smul,
        zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
      have h3 := (pow_iff Xo (N ^ 2) (u b)).mpr h2
      rw [mul_pow, _root_.mul_comm, pow_mul, h3, one_pow]
    · obtain ⟨r, hr⟩ := exists_factor A mu hmu c cm hcm
      have h1 := hKl.mul r
      rw [hr] at h1
      exact (kills_iff Xo cm u).mpr (h1.cancel (cop _ (A.cop.pow_left 2)) tors)
end Pts

end GlobalTheory.ZPart

namespace GlobalTheory

theorem inZh_iff_kills_adapted :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n : ℕ) (Λ : GenLat E n) (N ℓ : ℕ), ℓ.Prime → 0 < N → ∀ (A : Adapt Λ N ℓ) (T : Over Xo.X) (u : Fin n → (T ⟶ Xo.univ.t.G)), (∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) → (InZh Xo Λ N u ↔ Kills Xo (A.p * A.q) u) ∧ (InZh Xo Λ (A.k * N) u ↔ Kills Xo (A.p * A.q) u) := by
  intro E _ _ _ H Dw l Xo n Λ N ℓ _ _ A T u hu
  refine ⟨?_, ZPart.inZh_iff Xo A u hu A.k A.cop⟩
  have h1 := ZPart.inZh_iff Xo A u hu 1 (Nat.coprime_one_left ℓ)
  rwa [Nat.one_mul] at h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBound
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.ChartBiext

theorem constantCoeff_gauge {R K O : Type} [CommRing R] [CommRing K] [Algebra ℚ K] [Algebra R K] [CommRing O] [StarRing O]
    {d : ℕ} (B : FB R d O) {h : PS K 2 d} (hh : B.IsCanonGauge K h) : MvPowerSeries.constantCoeff h = 0 := by
  have hz : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, pt K d 0] : Fin 2 → Pt K 1 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hz
  set c := MvPowerSeries.constantCoeff h with hc
  have hdec : h = MvPowerSeries.C c + (h - MvPowerSeries.C c) := by ring
  have hrest : MvPowerSeries.constantCoeff (h - MvPowerSeries.C c) = 0 := by simp [hc]
  have key := congrArg MvPowerSeries.constantCoeff hh.ax0
  rw [ev, hdec, MvPowerSeries.subst_add hsub, map_add (f := _),
    MvPowerSeries.constantCoeff_subst_eq_zero hsub hz hrest] at key
  simpa using key

theorem toK_self {K : Type} [CommRing K] {σ : Type} (f : MvPowerSeries σ K) :
    MvPowerSeries.map (algebraMap K K) f = f := by
  ext m
  simp

theorem nabValN_congr {R R' K O : Type} [CommRing R] [CommRing R'] [CommRing K] [Algebra ℚ K] [Algebra R K] [Algebra R' K]
    [CommRing O] [StarRing O] {d : ℕ} (B : FB R d O) (B' : FB R' d O) (hF : B.FK K = B'.FK K)
    (hA : ∀ a, B.actK K a = B'.actK K a) (h : PS K 2 d) (w0 : O) (m : ℕ) {n : ℕ} (f : PS K n d) {Ix : Type} [Fintype Ix]
    (cp : Ix → Fin n) (u : Ix → Fin d → K) (P : MvPolynomial Ix K) :
    nabValN B K h w0 m f cp u P = nabValN B' K h w0 m f cp u P := by
  simp only [nabValN, FB.hL, hF, hA]

end GlobalTheory.ChartBiext


open GlobalTheory.ChartBiext in
theorem GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∃ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B ∧ ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → B.IsCanonGauge T.Fr (gaugeOf C) ∧ MvPowerSeries.constantCoeff (gaugeOf C) = 0 ∧ (letI := io.toAlgebra; (∀ (ℓ : Lt1 Dw) (a : 𝓞 E), (dAct T.Fr B a).mulVec (C.ch.uvec ℓ) = io (embK c ℓ.1 a) • C.ch.uvec ℓ) ∧ ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ρ w n → ∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ g : PS T.V n (chD C.ch), ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr g) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P)) := by
  intro E _ _ _ H Dw l Xo c inst hstar T io y C

  have hinst : inst = H.starRing := by
    cases inst with
    | @mk toStarMul star_add =>
      cases toStarMul with
      | @mk toInvolutiveStar star_mul =>
        cases toInvolutiveStar with
        | @mk toStar star_involutive =>
          cases toStar with
          | @mk s =>
            have hs : s = fun a => H.bar a := funext hstar
            subst hs
            rfl
  subst hinst
  letI : StarRing (𝓞 E) := H.starRing
  obtain ⟨BT, hF, hA, h1, h2, hs, had, hK⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨hFK, hAK, hG, hC⟩ := hK T.Fr
  refine ⟨BT, ⟨hF, hA, h1, h2, hs, had⟩, ?_⟩
  intro B hB
  obtain ⟨hBF, hBA, hB1, hB2, hBs, hBa⟩ := hB

  have eFK : B.FK T.Fr = BT.FK T.Fr := by
    funext i
    show MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (BT.G.F i)
    rw [hBF, hF]
  have eAK : ∀ a, B.actK T.Fr a = BT.actK T.Fr a := by
    intro a
    funext i
    show MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (BT.A.act a i)
    rw [hBA, hA]
  have hgB : B.IsCanonGauge T.Fr (gaugeOf C) ↔ BT.IsCanonGauge T.Fr (gaugeOf C) :=
    GlobalTheory.FBDescent.gauge_iff B BT T.Fr eFK eAK (by rw [hB1, h1]) (by rw [hB2, h2]) (by rw [hBs, hs])
      (fun a => by rw [hBa, had]) (gaugeOf C)
  have hgT : BT.IsCanonGauge T.Fr (gaugeOf C) := by
    rw [GlobalTheory.ChartBiext.toK_self] at hC
    exact (hG _).2 hC
  have hgauge : B.IsCanonGauge T.Fr (gaugeOf C) := hgB.2 hgT
  refine ⟨hgauge, GlobalTheory.ChartBiext.constantCoeff_gauge B hgauge, ?_⟩
  letI := io.toAlgebra
  have eFK' : B.FK T.Fr = C.ch.B.FK T.Fr := eFK.trans hFK
  have eAK' : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := fun a => (eAK a).trans (hAK a)
  refine ⟨fun ℓ a => ?_, ?_⟩
  ·
    have hd : dAct T.Fr B a = dAct T.Fr C.ch.B a := by
      unfold dAct
      rw [eAK' a]
    rw [hd]
    exact GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y C a ℓ
  · intro e ρ w n hb k P hP g
    have hint : IsIntPS T (FB.toK T.Fr g) := fun m =>
      ⟨MvPowerSeries.coeff m g, by simp [FB.toK, MvPowerSeries.coeff_map]⟩
    have hle : nuLocC C e k w n ≤ nval T.V e (nabValN C.ch.B T.Fr C.ch.h H.w0 k (FB.toK T.Fr g)
        (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P) := by
      unfold nuLocC
      exact iInf₂_le_of_le P hP (iInf₂_le (FB.toK T.Fr g) hint)
    rw [GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eFK' eAK']
    exact (hb k).trans hle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InvariantsAndTraceFiniteFreeDomainEndomorphisms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem invariants_and_trace_of_card_eq_finrank :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (G : Finset (R →ₐ[A] R)), G.card = Module.finrank A R → (∀ x : R, (∀ g ∈ G, g x = x) → x ∈ (algebraMap A R).range) ∧ ∀ x : R, algebraMap A R (Algebra.trace A R x) = ∑ g ∈ G, g x := by
  classical
  intro A R _ _ _ _ _ _ _ G hG
  let b : Module.Basis G A R := (Module.finBasis A R).reindex
    (Fintype.equivOfCardEq (by simp [hG]))
  let M : Matrix G G R := Matrix.of fun g i => g.1 (b i)
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    have hli : LinearIndependent R (fun g : G => ((g.1 : R →* R) : R → R)) := by
      refine (linearIndependent_monoidHom R R).comp (fun g : G => (g.1 : R →* R)) ?_
      intro g g' hgg
      apply Subtype.ext
      ext x
      exact DFunLike.congr_fun hgg x
    apply hv
    funext g
    refine Fintype.linearIndependent_iff.1 hli v ?_ g
    have hz : (∑ g : G, v g • g.1.toLinearMap) = 0 := by
      apply b.ext
      intro i
      have := congrFun hvM i
      simpa [Matrix.vecMul, dotProduct, M] using this
    funext x
    have := LinearMap.congr_fun hz x
    simpa using this
  have key : ∀ x : R, Matrix.diagonal (fun g : G => g.1 x) * M =
      M * (Algebra.leftMulMatrix b x).map (algebraMap A R) := by
    intro x
    ext g j
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [M, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [← map_mul]
    conv_lhs => rw [← b.sum_repr (x * b j)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def, mul_comm]
  have key2 : ∀ x : R, M.adjugate * (Matrix.diagonal (fun g : G => g.1 x) * M) =
      M.det • (Algebra.leftMulMatrix b x).map (algebraMap A R) := by
    intro x
    rw [key, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨i⟩ : Nonempty G := b.index_nonempty
    have h1 : Matrix.diagonal (fun g : G => g.1 x) = x • (1 : Matrix G G R) := by
      rw [Matrix.smul_one_eq_diagonal]
      congr 1
      funext g
      exact hx g.1 g.2
    have h2 := key2 x
    rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.adjugate_mul] at h2
    have h3 := congrFun (congrFun h2 i) i
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one,
      Matrix.map_apply] at h3
    rw [mul_comm] at h3
    exact ⟨_, (mul_left_cancel₀ hdet h3).symm⟩
  · have h2 := congrArg Matrix.trace (key2 x)
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
      Matrix.trace_diagonal] at h2
    have h3 := mul_left_cancel₀ hdet h2
    rw [Algebra.trace_eq_matrix_trace b, ← Finset.sum_coe_sort G (fun g => g x), h3]
    simp [Matrix.trace]

end GlobalTheory.PlaceInt
end

