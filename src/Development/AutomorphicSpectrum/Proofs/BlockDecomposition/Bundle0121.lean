module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0110
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0100

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateShafarevichDualityH1
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.PoitouTateGlue

theorem range_localization_eq_annihilator (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ)
    (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
    (h : NineTermExact S Av μ j ρ hρ) :
    LinearMap.range (loc1 S Av ρ) =
      ⨅ y ∈ LinearMap.range (loc1 S Av (twDual μ ρ)), LinearMap.ker (sumPair S Av μ j ρ hρ y) := by
  obtain ⟨δ₁, δ₂, -, -, -, -, hex, -⟩ := h
  have key : ∀ z x, sumPair S Av μ j ρ hρ (loc1 S Av (twDual μ ρ) z) x =
      GlobalTheory.Published.PoitouTate.tr1 S Av μ j ρ hρ x z := by
    intro z x
    simp [sumPair, GlobalTheory.Published.PoitouTate.tr1, loc1, LinearMap.sum_apply]
  ext x
  rw [Submodule.mem_iInf]
  constructor
  · intro hx y
    rw [Submodule.mem_iInf]
    rintro ⟨z, rfl⟩
    rw [LinearMap.mem_ker, key, (hex x).mpr (LinearMap.mem_range.mp hx)]
    simp
  · intro hx
    obtain ⟨y, hy⟩ := (hex x).mp (LinearMap.ext fun z => by
      have hz := (Submodule.mem_iInf _).mp (hx (loc1 S Av (twDual μ ρ) z)) ⟨z, rfl⟩
      rw [LinearMap.mem_ker, key] at hz
      simpa using hz)
    exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.PoitouTateGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToConeSurjective
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ChartBij
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {n d : ℕ}

def coord (k : Fin d) (g : Gam n d) : E n d → ℤ
  | Sum.inl l => g (Sum.inl l)
  | Sum.inr j => if j = k then tdeg g else g (Sum.inr j)

theorem coord_add (k : Fin d) (g g' : Gam n d) : coord k (g + g') = coord k g + coord k g' := by
  funext e
  rcases e with l | j
  · rfl
  · by_cases h : j = k
    · simp [coord, h, tdeg_add]
    · simp [coord, h]

theorem coord_zero (k : Fin d) : coord k (0 : Gam n d) = 0 := by
  funext e
  rcases e with l | j
  · rfl
  · by_cases h : j = k
    · simp [coord, h, tdeg]
    · simp [coord, h]

theorem tdeg_ratE (k j : Fin d) : tdeg (ratE k j : Gam n d) = 0 := by
  have h1 := tdeg_add (ratE k j : Gam n d) (oneE (Sum.inr k))
  have h2 : (ratE k j : Gam n d) + oneE (Sum.inr k) = oneE (Sum.inr j) := by simp [ratE]
  rw [h2, tdeg_oneE_inr, tdeg_oneE_inr] at h1
  linarith

theorem coord_wv (k : Fin d) (e e' : E n d) : coord k (wv k e) e' = if e' = e then 1 else 0 := by
  rcases e with l | j <;> rcases e' with l' | j'
  · simp [coord, wv, oneE, Pi.single_apply]
  · by_cases h : j' = k
    · simp [coord, wv, oneE, h, tdeg, Pi.single_apply]
    · simp [coord, wv, oneE, h, Pi.single_apply]
  · by_cases h : j = k
    · simp [coord, wv, oneE, h, Pi.single_apply]
    · simp [coord, wv, ratE, oneE, h, Pi.single_apply]
  · by_cases h : j = k
    · subst h
      by_cases h' : j' = j
      · simp [coord, wv, h', tdeg_oneE_inr]
      · simp [coord, wv, oneE, h', Pi.single_apply]
    · by_cases h' : j' = k
      · subst h'
        have hne : ¬ j' = j := fun e => h e.symm
        simp [coord, wv, h, hne, tdeg_ratE]
      · by_cases h'' : j' = j
        · subst h''
          simp [coord, wv, ratE, oneE, h, h', Pi.single_apply]
        · simp [coord, wv, ratE, oneE, h, h', h'', Pi.single_apply]

theorem coord_inj (k : Fin d) {g g' : Gam n d} (h : coord k g = coord k g') : g = g' := by
  have hj : ∀ j, j ≠ k → g (Sum.inr j) = g' (Sum.inr j) := fun j hj => by
    have := congrFun h (Sum.inr j)
    simpa [coord, hj] using this
  have ht : tdeg g = tdeg g' := by
    have := congrFun h (Sum.inr k)
    simpa [coord] using this
  funext e
  rcases e with l | j
  · exact congrFun h (Sum.inl l)
  · by_cases hjk : j = k
    · subst hjk
      unfold tdeg at ht
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at ht
      have : ∑ x ∈ Finset.univ.erase j, g (Sum.inr x) = ∑ x ∈ Finset.univ.erase j, g' (Sum.inr x) :=
        Finset.sum_congr rfl fun x hx => hj x (Finset.ne_of_mem_erase hx)
      linarith
    · exact hj j hjk

def toCone (k : Fin d) : (E n d →₀ ℕ) →+ (cone {k} : AddSubmonoid (Gam n d)) :=
  Finsupp.liftAddHom fun e => multiplesHom _ ⟨wv k e, wv_mem (Finset.mem_singleton_self k) e⟩

theorem toCone_single (k : Fin d) (e : E n d) :
    toCone k (Finsupp.single e 1) = ⟨wv k e, wv_mem (Finset.mem_singleton_self k) e⟩ := by
  simp [toCone]

theorem coord_toCone (k : Fin d) (f : E n d →₀ ℕ) (e : E n d) :
    coord k (toCone k f : Gam n d) e = f e := by
  induction f using Finsupp.induction_linear with
  | zero => simp [coord_zero]
  | add f g hf hg =>
    rw [map_add (f := _), AddSubmonoid.coe_add, coord_add, Pi.add_apply, hf, hg]
    simp
  | single a b =>
    induction b with
    | zero => simp [coord_zero]
    | succ b ih =>
      rw [show Finsupp.single a (b + 1) = Finsupp.single a b + Finsupp.single a 1 by simp,
        map_add, AddSubmonoid.coe_add, coord_add, Pi.add_apply, ih, toCone_single]
      simp only [coord_wv, Finsupp.add_apply, Finsupp.single_apply]
      by_cases h : e = a
      · simp [h]
      · have : ¬ a = e := fun x => h x.symm
        simp [h, this]

theorem toCone_injective (k : Fin d) : Function.Injective (toCone k : (E n d →₀ ℕ) → _) := by
  intro f f' h
  ext e
  have h1 := coord_toCone k f e
  rw [h, coord_toCone] at h1
  exact_mod_cast h1.symm

theorem coord_nonneg (k : Fin d) {g : Gam n d} (hg : g ∈ (cone {k} : AddSubmonoid (Gam n d))) (e : E n d) :
    0 ≤ coord k g e := by
  rcases e with l | j
  · exact hg.1 l
  · by_cases h : j = k
    · simpa [coord, h] using hg.2.2
    · simpa [coord, h] using hg.2.1 j (by simpa using h)

theorem toCone_surjective (k : Fin d) : Function.Surjective (toCone k : (E n d →₀ ℕ) → _) := by
  rintro ⟨g, hg⟩
  refine ⟨Finsupp.equivFunOnFinite.symm fun e => (coord k g e).toNat, Subtype.ext (coord_inj k ?_)⟩
  funext e
  rw [coord_toCone]
  simpa using coord_nonneg k hg e

def coneEquiv (k : Fin d) : (E n d →₀ ℕ) ≃+ (cone {k} : AddSubmonoid (Gam n d)) :=
  AddEquiv.ofBijective (toCone k) ⟨toCone_injective k, toCone_surjective k⟩

theorem chart_bijective {K : Type} [Field K] {n d : ℕ} (k : Fin d) :
    Function.Bijective (MvPolynomial.aeval (R := K)
      (fun e : E n d => mon K (wv k e) (wv_mem (Finset.mem_singleton_self k) e)) : Bp K n d →ₐ[K] R0 K n d {k}) := by
  let Φ : Bp K n d ≃ₐ[K] R0 K n d {k} := AddMonoidAlgebra.domCongr K K (coneEquiv k)
  have h : (MvPolynomial.aeval (R := K)
      (fun e : E n d => mon K (wv k e) (wv_mem (Finset.mem_singleton_self k) e)) : Bp K n d →ₐ[K] R0 K n d {k}) = Φ.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro e
    rw [MvPolynomial.aeval_X]
    change _ = AddMonoidAlgebra.domCongr K K (coneEquiv k) (AddMonoidAlgebra.single (Finsupp.single e 1) 1)
    simp only [mon, coneEquiv]
    simp
    exact congrArg (fun m => AddMonoidAlgebra.single m (1 : K)) (toCone_single k e).symm
  rw [h]
  exact Φ.bijective

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ChartBij
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormula
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens Filter Topology

namespace GlobalTheory.CompanionTheory.UnrDens

theorem unrFormula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  intro R _ σ ϖ q ε hR m n hnm S T hS hT
  have hq : (0 : ℝ) < q := by exact_mod_cast lt_trans zero_lt_one hR.one_lt
  have hsq : n ^ 2 ≤ 2 * m * n := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, 2 * m * n - n ^ 2 = a := ⟨_, rfl⟩
  have ha' : a + n ^ 2 = 2 * m * n := by omega
  have hsol : ∀ j : ℕ, (solCount σ ϖ S T (j + 1) : ℝ) =
      (q : ℝ) ^ a * (∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) * (q : ℝ) ^ (j * a) := by
    intro j
    induction j with
    | zero =>
      rw [_root_.GlobalTheory.CompanionTheory.UnrDens.solCount_one R σ ϖ q ε hR m n hnm S T hS hT, ha]
      simp
    | succ j ih =>
      rw [_root_.GlobalTheory.CompanionTheory.UnrDens.solCount_succ R σ ϖ q ε hR m n hnm S T hS hT (j + 1) (by omega), ha]
      push_cast
      rw [ih, add_mul, one_mul, pow_add]
      ring
  have hdens : ∀ j : ℕ, densAt σ ϖ S T (j + 1) = ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
    intro j
    unfold densAt
    have hM : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (j + 1))) = q ^ (2 * (j + 1) * (m * n)) := by
      show Nat.card (Fin m → Fin n → R ⧸ lev ϖ (j + 1)) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, _root_.GlobalTheory.CompanionTheory.UnrDens.card_quot_lev R σ ϖ q ε hR (j + 1), ← pow_mul,
        ← pow_mul]
      ring_nf
    rw [hsol j, _root_.GlobalTheory.CompanionTheory.UnrDens.card_hermMod R σ ϖ q ε hR n (j + 1), hM]
    have he : a + j * a + (j + 1) * n ^ 2 = 2 * (j + 1) * (m * n) := by
      calc a + j * a + (j + 1) * n ^ 2 = (j + 1) * (a + n ^ 2) := by ring
        _ = (j + 1) * (2 * m * n) := by rw [ha']
        _ = 2 * (j + 1) * (m * n) := by ring
    have hpos : (0 : ℝ) < (q : ℝ) ^ (2 * (j + 1) * (m * n)) := pow_pos hq _
    push_cast
    rw [div_eq_iff hpos.ne', ← he, pow_add, pow_add]
    ring
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (hdens j).symm

end GlobalTheory.CompanionTheory.UnrDens
end

