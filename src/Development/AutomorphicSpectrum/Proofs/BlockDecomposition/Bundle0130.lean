module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonLNegOneEMul
section
set_option autoImplicit false
noncomputable section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis

def allE {n d : ℕ} : Gam n d := ∑ e, oneE e

theorem allE_mem {n d : ℕ} : (allE : Gam n d) ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  unfold allE
  exact AddSubmonoid.sum_mem _ (fun e _ => oneE_mem ∅ e)

theorem allE_apply {n d : ℕ} (e : E n d) : (allE : Gam n d) e = 1 := by
  unfold allE
  rw [Finset.sum_apply]
  simp [oneE, Pi.single_apply]

theorem exists_add_mem {n d : ℕ} (g : Gam n d) :
    ∃ N : ℕ, g + N • allE ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  refine ⟨∑ e, (g e).natAbs, ?_⟩
  have hnn : ∀ e, 0 ≤ (g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e := by
    intro e
    have h1 : (g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e
        = g e + ((∑ e, (g e).natAbs : ℕ) : ℤ) := by
      change g e + (∑ e, (g e).natAbs) • (allE : Gam n d) e = _
      rw [allE_apply, nsmul_one]
    have h2 : (g e).natAbs ≤ ∑ e, (g e).natAbs :=
      Finset.single_le_sum (f := fun e => (g e).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ e)
    have h3 : ((g e).natAbs : ℤ) ≤ ((∑ e, (g e).natAbs : ℕ) : ℤ) := by exact_mod_cast h2
    rw [h1]
    have h4 := Int.natCast_natAbs (g e)
    have h5 := neg_abs_le (g e)
    linarith
  have key := PolyBij.coe_mem_cone (n := n) (d := d)
    (Finsupp.equivFunOnFinite.symm fun e => ((g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e).toNat)
  convert key using 2
  rename_i e
  exact (Int.toNat_of_nonneg (hnn e)).symm

theorem monL_neg_oneE_mul {K : Type} [Field K] {n d : ℕ} (e : E n d) : monL K (-oneE e) * monL K (oneE e) = 1 := by
  rw [monL, monL, mon_mul]
  change AddMonoidAlgebra.single _ (1 : K) = AddMonoidAlgebra.single 0 1
  congr 1
  exact Subtype.ext (neg_add_cancel (oneE e))

theorem exists_basis_dl : ∀ {K : Type} [Field K] {n d : ℕ},
    ∃ b : Module.Basis (E n d) (Lr K n d) Ω[Lr K n d⁄K], ∀ e, b e = dl e := by
  intro K _ n d
  have hle : (cone ∅ : AddSubmonoid (Gam n d)) ≤ ⊤ := le_top
  let φ : MvPolynomial (E n d) K →ₐ[K] Lr K n d := (incl (K := K) hle).comp (poly n K ∅)
  letI : Algebra (MvPolynomial (E n d) K) (Lr K n d) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (E n d) K) (Lr K n d) := IsScalarTower.of_algHom φ
  let s0 : MvPolynomial (E n d) K := (PolyBij.polyEquiv K).symm (mon K (allE : Gam n d) allE_mem)
  have hpe : ∀ a, poly n K ∅ ((PolyBij.polyEquiv (n := n) (d := d) K).symm a) = a := by
    intro a
    rw [PolyBij.poly_eq_polyEquiv, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  have e1 : φ s0 = incl (K := K) hle (mon K (allE : Gam n d) allE_mem) := by
    change incl (K := K) hle (poly n K ∅ s0) = _
    rw [hpe]
  have hmul : φ s0 * mon K (-(allE : Gam n d)) (AddSubmonoid.mem_top _) = 1 := by
    rw [e1, incl_mon, mon_mul]
    change AddMonoidAlgebra.single _ (1 : K) = AddMonoidAlgebra.single 0 1
    congr 1
    exact Subtype.ext (add_neg_cancel (allE : Gam n d))
  have hunit : IsUnit (φ s0) := ⟨⟨φ s0, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  have hinj : Function.Injective φ :=
    (Away.incl_injective (K := K) hle).comp (PolyBij.poly_bijective (K := K) (n := n) (d := d)).1
  haveI : IsLocalization (Submonoid.powers s0) (Lr K n d) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      rw [← hk]
      change IsUnit (φ (s0 ^ k))
      rw [map_pow]
      exact hunit.pow k
    · intro z
      obtain ⟨N, a, ha⟩ := Away.exists_mul_pow_eq_incl (K := K) hle (allE : Gam n d) allE_mem
        (fun g _ => exists_add_mem g) z
      refine ⟨((PolyBij.polyEquiv K).symm a, ⟨s0 ^ N, N, rfl⟩), ?_⟩
      change z * φ (s0 ^ N) = φ ((PolyBij.polyEquiv K).symm a)
      have e2 : φ ((PolyBij.polyEquiv K).symm a) = incl (K := K) hle a := by
        change incl (K := K) hle (poly n K ∅ _) = _
        rw [hpe]
      rw [map_pow, e1, e2, ← map_pow]
      exact ha
    · intro x y hxy
      have hxy' : φ x = φ y := hxy
      exact ⟨1, by rw [hinj hxy']⟩
  let b0 := (KaehlerDifferential.mvPolynomialBasis K (E n d)).ofIsLocalizedModule (Lr K n d)
    (Submonoid.powers s0) (KaehlerDifferential.map K K (MvPolynomial (E n d) K) (Lr K n d))
  let w : E n d → (Lr K n d)ˣ := fun e =>
    ⟨monL K (-oneE e), monL K (oneE e), monL_neg_oneE_mul e, by rw [mul_comm]; exact monL_neg_oneE_mul e⟩
  refine ⟨b0.unitsSMul w, fun e => ?_⟩
  have e4 : KaehlerDifferential.mvPolynomialBasis K (E n d) e
      = KaehlerDifferential.D K (MvPolynomial (E n d) K) (MvPolynomial.X e) :=
    Module.Basis.apply_eq_iff.mpr (by rw [KaehlerDifferential.mvPolynomialBasis_repr_D_X])
  rw [Module.Basis.unitsSMul_apply, Module.Basis.ofIsLocalizedModule_apply, e4, KaehlerDifferential.map_D]
  have e3 : φ (MvPolynomial.X e) = monL K (oneE e) := by
    change incl (K := K) hle (poly n K ∅ (MvPolynomial.X e)) = _
    rw [poly_X, incl_mon]
    rfl
  change monL K (-oneE e) • KaehlerDifferential.D K (Lr K n d) (φ (MvPolynomial.X e)) = dl e
  rw [e3]
  rfl

end GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace GlobalTheory.CompanionTheory.PTIso

section Gen

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {I : Type} [Fintype I] {D : I → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
  (χ : Γ →* Rˣ)
  (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R)
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M)

def gloc0 : H0 ρ →ₗ[R] ∀ i, H0 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH0 ρ (φ i)

def gloc1 : H1 ρ →ₗ[R] ∀ i, H1 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH1 ρ (φ i) (hφ i)

def gloc2 : H2 ρ →ₗ[R] ∀ i, H2 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH2 ρ (φ i) (hφ i)

def gtr0 : (∀ i, H0 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H2 (twDual χ ρ)) :=
  ∑ i, (((cupH0H2TwistedDual χ ρ (φ i)).compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH2 (twDual χ ρ) (φ i) (hφ i)))

def gtr1 (hρ : ContAction ρ) : (∀ i, H1 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H1 (twDual χ ρ)) :=
  ∑ i, (((cupH1H1TwistedDual χ ρ (φ i) (hρ.comp' (hφ i))).flip.compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH1 (twDual χ ρ) (φ i) (hφ i)))

def gtr2 : (∀ i, H2 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H0 (twDual χ ρ)) :=
  ∑ i, (((cup20 χ ρ (φ i)).compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH0 (twDual χ ρ) (φ i)))

def NineG (hρ : ContAction ρ) : Prop :=
  ∃ (δ₁ : Module.Dual R (H2 (twDual χ ρ)) →ₗ[R] H1 ρ)
    (δ₂ : Module.Dual R (H1 (twDual χ ρ)) →ₗ[R] H2 ρ),
    Function.Injective (gloc0 φ ρ) ∧
    Function.Exact (gloc0 φ ρ) (gtr0 φ hφ χ j ρ) ∧
    Function.Exact (gtr0 φ hφ χ j ρ) δ₁ ∧
    Function.Exact δ₁ (gloc1 φ hφ ρ) ∧
    Function.Exact (gloc1 φ hφ ρ) (gtr1 φ hφ χ j ρ hρ) ∧
    Function.Exact (gtr1 φ hφ χ j ρ hρ) δ₂ ∧
    Function.Exact δ₂ (gloc2 φ hφ ρ) ∧
    Function.Exact (gloc2 φ hφ ρ) (gtr2 φ χ j ρ) ∧
    Function.Surjective (gtr2 φ χ j ρ)

def ShaG : Prop :=
  (Finite (Sha1 (twDual χ ρ) φ hφ) ∧ Finite (Sha2 ρ φ hφ) ∧
    Nonempty (Sha2 ρ φ hφ ≃ₗ[R] Module.Dual R (Sha1 (twDual χ ρ) φ hφ)) ∧
    Nat.card (Sha1 (twDual χ ρ) φ hφ) = Nat.card (Sha2 ρ φ hφ)) ∧
  (Finite (Sha1 ρ φ hφ) ∧ Finite (Sha2 (twDual χ ρ) φ hφ) ∧
    Nonempty (Sha2 (twDual χ ρ) φ hφ ≃ₗ[R] Module.Dual R (Sha1 ρ φ hφ)) ∧
    Nat.card (Sha1 ρ φ hφ) = Nat.card (Sha2 (twDual χ ρ) φ hφ))

end Gen

section Concrete

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

theorem nineTermExact_iff (hρ : ContAction ρ) :
    NineTermExact S Av μ j ρ hρ ↔
      NineG (locFam S Av) (continuous_locFam S Av) μ j ρ hρ := Iff.rfl

theorem shaDual_iff :
    ShaDual S Av μ ρ ↔ ShaG (locFam S Av) (continuous_locFam S Av) μ ρ := Iff.rfl

end Concrete

def subgroupIso {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]
    (Φ : A ≃ₜ* B) (H : Subgroup A) (K : Subgroup B) (h : ∀ a, a ∈ H ↔ Φ a ∈ K) : H ≃ₜ* K where
  toFun a := ⟨Φ a.1, (h a.1).1 a.2⟩
  invFun b := ⟨Φ.symm b.1, (h _).2 (by simpa using b.2)⟩
  left_inv a := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  continuous_toFun := (Φ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Φ.symm.continuous.comp continuous_subtype_val).subtype_mk _

end GlobalTheory.CompanionTheory.PTIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoitouTateNineTermExact
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.PoitouTateCount

theorem card_sha2_mul_card_local_h2 : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → NineTermExact S Av μ j ρ hρ → Finite (H2 ρ) → Finite (H0 (twDual μ ρ)) → Nat.card (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) * Nat.card (∀ v : S, H2 (ρ.comp (locFam S Av v))) = Nat.card (H2 ρ) * Nat.card (H0 (twDual μ ρ)) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ j hLF hr hAv hNine hH2 hH0
  obtain ⟨_δ₁, _δ₂, -, -, -, -, -, -, -, hex, hsurj⟩ := hNine
  haveI : ∀ v : S, Finite (H2 (ρ.comp (locFam S Av v))) := fun v =>
    (_root_.GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r M S Av μ ρ hρ hLF hr hAv v).2.2
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime l).ne_zero⟩
  have hsha : Sha2 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc2 S Av ρ) :=
    (_root_.GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker F Ω l r M S Av μ ρ hρ).2.2
  have h1 := GlobalTheory.CompanionTheory.Counting.card_eq_card_ker_mul_card_range (ZMod (l ^ r)) _ _ (loc2 S Av ρ)
  have h2 := GlobalTheory.CompanionTheory.Counting.card_eq_card_ker_mul_card_range (ZMod (l ^ r)) _ _ (tr2 S Av μ j ρ)
  have hker : LinearMap.ker (tr2 S Av μ j ρ) = LinearMap.range (loc2 S Av ρ) := LinearMap.exact_iff.mp hex
  have htop : LinearMap.range (tr2 S Av μ j ρ) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have htopc : Nat.card ↥(⊤ : Submodule (ZMod (l ^ r)) (Module.Dual (ZMod (l ^ r)) ↥(H0 (twDual μ ρ)))) =
      Nat.card (Module.Dual (ZMod (l ^ r)) ↥(H0 (twDual μ ρ))) :=
    Nat.card_congr Submodule.topEquiv.toEquiv
  have hD := GlobalTheory.CompanionTheory.ZModDual.nat_card_dual_eq (l ^ r) ↥(H0 (twDual μ ρ))
  rw [hsha, h2, hker, htop, htopc, hD, h1]
  ring

end GlobalTheory.CompanionTheory.PoitouTateCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackZeroCochainsAlgebraMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeLow

theorem qIsoAt_transport {R A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂']
    [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [Module R A₀'] [Module R A₁'] [Module R A₂'] [Module R B₀'] [Module R B₁'] [Module R B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[R] A₁'} {a₁' : A₁' →ₗ[R] A₂'} {b₀' : B₀' →ₗ[R] B₁'} {b₁' : B₁' →ₗ[R] B₂'}
    {f' : A₁' →ₗ[R] B₁'}
    (ea₀ : A₀ ≃ₗ[R] A₀') (ea₁ : A₁ ≃ₗ[R] A₁') (ea₂ : A₂ ≃ₗ[R] A₂')
    (eb₀ : B₀ ≃ₗ[R] B₀') (eb₁ : B₁ ≃ₗ[R] B₁') (eb₂ : B₂ ≃ₗ[R] B₂')
    (ha₀ : ∀ x, ea₁ (a₀ x) = a₀' (ea₀ x)) (ha₁ : ∀ x, ea₂ (a₁ x) = a₁' (ea₁ x))
    (hb₀ : ∀ x, eb₁ (b₀ x) = b₀' (eb₀ x)) (hb₁ : ∀ x, eb₂ (b₁ x) = b₁' (eb₁ x))
    (hf : ∀ x, eb₁ (f x) = f' (ea₁ x)) (h : QIsoAt a₀ a₁ b₀ b₁ f) :
    QIsoAt a₀' a₁' b₀' b₁' f' := by
  refine ⟨fun x' hx' ⟨y', hy'⟩ ↦ ?_, fun z' hz' ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := ea₁.surjective x'
    obtain ⟨y, rfl⟩ := eb₀.surjective y'
    have h1 : a₁ x = 0 := ea₂.injective (by rw [ha₁, hx', map_zero])
    have h2 : b₀ y = f x := eb₁.injective (by rw [hb₀, hy', hf])
    obtain ⟨w, rfl⟩ := h.1 x h1 ⟨y, h2⟩
    exact ⟨ea₀ w, (ha₀ w).symm⟩
  · obtain ⟨z, rfl⟩ := eb₁.surjective z'
    have h1 : b₁ z = 0 := eb₂.injective (by rw [hb₁, hz', map_zero])
    obtain ⟨x, y, hx, hy⟩ := h.2 z h1
    refine ⟨ea₁ x, eb₀ y, by rw [← ha₁, hx, map_zero], ?_⟩
    rw [← hf, ← map_sub, hy, hb₀]

section

variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}

theorem d2_apply (z : C2 F) {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ +
      z T T' T''' φ (ψ ≫ χ) - mp F χ (z T T' T'' φ ψ) := rfl

theorem mem_Z2_iff (z : C2 F) : z ∈ Z2 F ↔ d2 F z = 0 := by
  refine ⟨fun h ↦ ?_, fun h T T' T'' T''' φ ψ χ ↦ ?_⟩
  · funext T T' T'' T''' φ ψ χ
    rw [d2_apply]
    have := h φ ψ χ
    simp only [Pi.zero_apply]
    linear_combination -this
  · have : d2 F z T T' T'' T''' φ ψ χ = 0 := by rw [h]; rfl
    rw [d2_apply] at this
    linear_combination -this

def pullbackZeroCochains (m : CoefMap (RingHom.id R) F F') : C0 F →ₗ[R] C0 F' where
  toFun g T := m.α T (g (m.G.obj T))
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := funext fun _ ↦ m.smul _ _ _

def pullbackOneCochains (m : CoefMap (RingHom.id R) F F') : C1 F →ₗ[R] C1 F' where
  toFun f T T' φ := m.α T' (f _ _ (m.G.map φ))
  map_add' _ _ := by funext T T' φ; exact map_add _ _ _
  map_smul' _ _ := by funext T T' φ; exact m.smul _ _ _

def pullbackTwoCochains (m : CoefMap (RingHom.id R) F F') : C2 F →ₗ[R] C2 F' where
  toFun z T T' T'' φ ψ := m.α T'' (z _ _ _ (m.G.map φ) (m.G.map ψ))
  map_add' _ _ := by funext T T' T'' φ ψ; exact map_add _ _ _
  map_smul' _ _ := by funext T T' T'' φ ψ; exact m.smul _ _ _

theorem cn_heq {n : ℕ} (f : Cn F n) {c c' : Fin (n + 1) ⥤ C} (h : c = c') : HEq (f c) (f c') := by
  subst h; rfl

theorem mk₀_comp (G : C' ⥤ C) (T : C') :
    ComposableArrows.mk₀ T ⋙ G = ComposableArrows.mk₀ (G.obj T) :=
  ComposableArrows.ext (fun i ↦ by fin_cases i; rfl) (fun i hi ↦ by omega)

theorem mk₁_comp (G : C' ⥤ C) {T T' : C'} (φ : T ⟶ T') :
    ComposableArrows.mk₁ φ ⋙ G = ComposableArrows.mk₁ (G.map φ) :=
  ComposableArrows.ext₁ rfl rfl (by
    change G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _
    simp)

theorem mk₂_comp (G : C' ⥤ C) {T T' T'' : C'} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    ComposableArrows.mk₂ φ ψ ⋙ G = ComposableArrows.mk₂ (G.map φ) (G.map ψ) :=
  ComposableArrows.ext (fun i ↦ by fin_cases i <;> rfl) (fun i hi ↦ by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · change G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _
      simp
    · change G.map ψ = 𝟙 _ ≫ G.map ψ ≫ 𝟙 _
      simp)

theorem pull1_bijective (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (d0 F) (d1 F) (d0 F') (d1 F') (pullbackOneCochains m)) : Function.Bijective m.pull1 := by
  refine ⟨(injective_iff_map_eq_zero m.pull1).2 fun c hc ↦ ?_, fun c' ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class] at hc
    obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
    have hf : d1 F f.1 = 0 := LinearMap.mem_ker.1 (commAlgFunctorCocyclesOne_eq_ker F ▸ f.2)
    obtain ⟨y, hy⟩ := h.1 f.1 hf ⟨g, hg⟩
    exact H1.mk_eq_zero.2 ⟨y, hy⟩
  · obtain ⟨f', rfl⟩ := H1.mk_surjective F' c'
    have hf : d1 F' f'.1 = 0 := LinearMap.mem_ker.1 (commAlgFunctorCocyclesOne_eq_ker F' ▸ f'.2)
    obtain ⟨x, y, hx, hy⟩ := h.2 f'.1 hf
    have hxm : x ∈ Z1 F := by rw [commAlgFunctorCocyclesOne_eq_ker]; exact hx
    refine ⟨H1.mk F ⟨x, hxm⟩, ?_⟩
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
    exact ⟨y, hy.symm⟩

theorem pull2_bijective (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (d1 F) (d2 F) (d1 F') (d2 F') (pullbackTwoCochains m)) : Function.Bijective m.pull2 := by
  refine ⟨(injective_iff_map_eq_zero m.pull2).2 fun c hc ↦ ?_, fun c' ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H2.mk_surjective F c
    rw [CoefMap.pullCohomologyTwo_class] at hc
    obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 hc
    obtain ⟨y, hy⟩ := h.1 f.1 ((mem_Z2_iff _).1 f.2) ⟨g, hg⟩
    exact H2.mk_eq_zero.2 ⟨y, hy⟩
  · obtain ⟨f', rfl⟩ := H2.mk_surjective F' c'
    obtain ⟨x, y, hx, hy⟩ := h.2 f'.1 ((mem_Z2_iff _).1 f'.2)
    refine ⟨H2.mk F ⟨x, (mem_Z2_iff _).2 hx⟩, ?_⟩
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
    exact ⟨y, hy.symm⟩

theorem pullbackZeroCochains_algebraMap (m : CoefMap (RingHom.id R) F F') (r : R) :
    pullbackZeroCochains m (algebraMap R (C0 F) r) = algebraMap R (C0 F') r := by
  funext T
  change m.α T (algebraMap R _ r) = algebraMap R _ r
  rw [Algebra.algebraMap_eq_smul_one, m.smul, map_one, Algebra.algebraMap_eq_smul_one]
  rfl

theorem d0_algebraMap (r : R) : d0 F (algebraMap R (C0 F) r) = 0 := by
  funext T T' φ
  rw [amitsur_d0_apply]
  change algebraMap R _ r - mp F φ (algebraMap R _ r) = 0
  rw [AlgHom.commutes, sub_self]

theorem d0_pullbackZeroCochains (m : CoefMap (RingHom.id R) F F') (g : C0 F) :
    d0 F' (pullbackZeroCochains m g) = pullbackOneCochains m (d0 F g) := by
  funext T T' φ
  change m.α T' (g _) - mp F' φ (m.α T (g _)) = m.α T' (g _ - mp F (m.G.map φ) (g _))
  rw [map_sub, m.naturality]

theorem stein_iff (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (0 : R →ₗ[R] C0 F) (d0 F) (0 : R →ₗ[R] C0 F') (d0 F') (pullbackZeroCochains m)) :
    Stein F ↔ Stein F' := by
  have hk : ∀ x, d0 F x = 0 → pullbackZeroCochains m x = 0 → x = 0 := fun x hx hp ↦ by
    obtain ⟨y, hy⟩ := h.1 x hx ⟨0, by rw [hp]; rfl⟩
    exact hy.symm
  have hs : ∀ z, d0 F' z = 0 → ∃ x, d0 F x = 0 ∧ pullbackZeroCochains m x = z := fun z hz ↦ by
    obtain ⟨x, y, hx, hy⟩ := h.2 z hz
    exact ⟨x, hx, sub_eq_zero.1 hy⟩
  constructor
  · rintro ⟨he, hi⟩
    refine ⟨fun y ↦ ⟨fun hy ↦ ?_, ?_⟩, fun r r' hr ↦ hi ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hs y hy
      obtain ⟨r, rfl⟩ := (he x).1 hx
      exact ⟨r, (pullbackZeroCochains_algebraMap m r).symm⟩
    · rintro ⟨r, rfl⟩
      exact d0_algebraMap r
    · rw [← sub_eq_zero, ← map_sub]
      refine hk _ (d0_algebraMap _) ?_
      rw [pullbackZeroCochains_algebraMap, map_sub, hr, sub_self]
  · rintro ⟨he, hi⟩
    refine ⟨fun y ↦ ⟨fun hy ↦ ?_, ?_⟩, fun r r' hr ↦ hi ?_⟩
    · have h0 : d0 F' (pullbackZeroCochains m y) = 0 := by rw [d0_pullbackZeroCochains, hy, map_zero]
      obtain ⟨r, hr⟩ := (he _).1 h0
      refine ⟨r, ?_⟩
      have hr' : algebraMap R (C0 F') r = pullbackZeroCochains m y := hr
      have e : y - algebraMap R (C0 F) r = 0 := hk _ (by rw [map_sub, hy, d0_algebraMap, sub_self])
        (by rw [map_sub, pullbackZeroCochains_algebraMap, hr', sub_self])
      exact (sub_eq_zero.1 e).symm
    · rintro ⟨r, rfl⟩
      exact d0_algebraMap r
    · rw [← pullbackZeroCochains_algebraMap m, ← pullbackZeroCochains_algebraMap m, hr]

end

theorem lowSt_of_dictSt : DictSt → LowSt := by
  intro hD R _ C C' _ _ F F' m hQ
  obtain ⟨e₀, e₁, e₂, e₃, v₀, v₁, v₂, v₃, c₀, c₁, c₂⟩ := hD R C F
  obtain ⟨e₀', e₁', e₂', e₃', v₀', v₁', v₂', v₃', c₀', c₁', c₂'⟩ := hD R C' F'
  have p0 : ∀ f, e₀' (pulln m 0 f) = pullbackZeroCochains m (e₀ f) := fun f ↦ by
    funext T
    rw [v₀']
    change m.α T (f (ComposableArrows.mk₀ T ⋙ m.G)) = m.α T (e₀ f (m.G.obj T))
    rw [v₀]
    exact congrArg (m.α T) (eq_of_heq (cn_heq f (mk₀_comp m.G T)))
  have p1 : ∀ f, e₁' (pulln m 1 f) = pullbackOneCochains m (e₁ f) := fun f ↦ by
    funext T T' φ
    rw [v₁']
    change m.α T' (f (ComposableArrows.mk₁ φ ⋙ m.G)) = m.α T' (e₁ f _ _ (m.G.map φ))
    rw [v₁]
    exact congrArg (m.α T') (eq_of_heq (cn_heq f (mk₁_comp m.G φ)))
  have p2 : ∀ f, e₂' (pulln m 2 f) = pullbackTwoCochains m (e₂ f) := fun f ↦ by
    funext T T' T'' φ ψ
    rw [v₂']
    change m.α T'' (f (ComposableArrows.mk₂ φ ψ ⋙ m.G)) = m.α T'' (e₂ f _ _ _ (m.G.map φ) (m.G.map ψ))
    rw [v₂]
    exact congrArg (m.α T'') (eq_of_heq (cn_heq f (mk₂_comp m.G φ ψ)))
  refine ⟨pull1_bijective m ?_, pull2_bijective m ?_, stein_iff m ?_⟩
  · exact qIsoAt_transport e₀ e₁ e₂ e₀' e₁' e₂' c₀ c₁ c₀' c₁' p1 (hQ.2 0)
  · exact qIsoAt_transport e₁ e₂ e₃ e₁' e₂' e₃' c₁ c₂ c₁' c₂' p2 (hQ.2 1)
  · exact qIsoAt_transport (LinearEquiv.refl R R) e₀ e₁ (LinearEquiv.refl R R) e₀' e₁'
      (fun _ ↦ map_zero _) c₀ (fun _ ↦ map_zero _) c₀' p0 hQ.1

end GlobalTheory.CompanionTheory.HodgeLow
end
end

