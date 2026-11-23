module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0015
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1IdentityLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0023
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0016
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0009
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RdBase
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExists
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeMonoLatticeLe
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem deg_le_deg_of_le : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' :=
  @PositivityTheory.HtPt.Ch.deg_mono

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DotDualSubDegreeAnnihilator
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_dotDual_orth : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W :=
  PositivityTheory.HtPt.Ch.subdeg_orth

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalBilinearTermProduct
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.BilCalc

theorem bil_calc : ∀ (R : Type) [CommRing R] (d : ℕ) (f g : PS R 2 d) (φ ψ : Pt R 1 d), AxOne f → AxOne g → (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → AxOne (f * g) ∧ (∀ m, bil (f * g) m 1 = bil f m 1 + bil g m 1) ∧ (∀ n, bil (f * g) 1 n = bil f 1 n + bil g 1 n) ∧ AxOne (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) ∧ bil (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) 1 1 = (lin φ 1).transpose * bil f 1 1 * lin ψ 1 ∧ (∀ m n, bil (ev (n := 2) ![pt R d 1, pt R d 0] f) m n = (bil f n m).transpose) ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → bil (ev (n := 2) ![ptPow R d m 0, ptPow R d n 1] f) m n = bil f 1 1 :=
  @PositivityTheory.HtPt.Ca.bil_calc

end GlobalTheory.CompanionTheory.Ar.Conj.BilCalc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalLinearTermCompositionStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_linear_term_composition : ∀ (R : Type) [CommRing R] (d : ℕ) (φ ψ : Pt R 1 d), (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → lin (comp1 φ ψ) 1 = lin φ 1 * lin ψ 1 ∧ lin (pt R (n := 1) d 0) 1 = 1 ∧ ∀ p : ℕ, 1 ≤ p → lin (comp1 φ (ptPow R d p 0)) p = lin φ 1 ∧ lin (comp1 φ (comp1 ψ (ptPow R d p 0))) p = lin φ 1 * lin ψ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.lin_comp_chain | exact GlobalTheory.CompanionTheory.Ar.Conj.lin_comp_chain | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.lin_comp_chain <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalModuleActionLaws
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.NatAct

theorem act_nat_iterated : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), B.A.act 0 = 0 ∧ (∀ n : ℕ, B.A.act ((n + 1 : ℕ) : O) = B.G.add (B.A.act (n : O)) (pt R d 0)) ∧ (∀ a b, comp1 (B.A.act a) (B.A.act b) = comp1 (B.A.act b) (B.A.act a)) ∧ ∀ n, AxOne (pow1 B n) ∧ AxOne (pow2 B n) :=
  @PositivityTheory.HtPt.Ca.act_zero

end GlobalTheory.CompanionTheory.Ar.Conj.NatAct
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHoldsStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_annihilator_lattice_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → ∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice | exact GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDifferentGenerators
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem gram_integral_unit_mod : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → ∃ G H Z Z' : Matrix (Fin N) (Fin N) A, (∀ i j, algebraMap A K (G i j) = D.gram σ d i j) ∧ G * H = 1 + ((p : A) ^ R) • Z ∧ H * G = 1 + ((p : A) ^ R) • Z' :=
  @PositivityTheory.HtPt.Ga.gram_unit

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDivisibility
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem q_onto_eigenpart_mod_pow : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' :=
  PositivityTheory.HtPt.Ga.q_surj

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderIdealsEqTop
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, idealX AA.carrier K t χ = ⊤ → ∃ τ : MulChar F R, IsFund p τ ∧ idealD p AA.carrier K t τ = ⊤ := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hFS K t ht hGen χ hχ
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hval : ∀ g ∈ AA.carrier, ∀ x, ∃ r : R, algebraMap R C r = g x := fun g hg =>
    (show ∀ x, ∃ r : R, algebraMap R C r = g x from AA.le_int hg)
  have hle : ∀ g ∈ AA.carrier, ∀ x, v (g x) ≤ 1 := by
    intro g hg x
    obtain ⟨r, hr⟩ := hval g hg x
    rw [← hr]
    exact hv.map_le_one r
  have hpv : ∀ z ∈ pInt (C := C) R p, v z < 1 := by
    intro z hz
    unfold pInt at hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [Algebra.smul_def, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hv.map_le_one a)) hp
  have hinv : ∀ g, g ∈ invFun AA.carrier K.toAddSubgroup →
      g ∈ AA.carrier ∧ ∀ x, ∀ k ∈ K.toAddSubgroup, g (x + k) = g x := fun g hg => hg
  have hinvI : ∀ g, (g ∈ AA.carrier ∧ ∀ x, ∀ k ∈ K.toAddSubgroup, g (x + k) = g x) →
      g ∈ invFun AA.carrier K.toAddSubgroup := fun g hg => hg
  have hadd : ∀ g, g ∈ addFun (C := C) R p N →
      ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) R p := fun g hg => hg
  have h1 : (1 : R) ∈ idealX AA.carrier K t χ := by
    rw [hχ]
    exact Submodule.mem_top
  obtain ⟨g0, hg0, hg0e⟩ := Submodule.mem_map.1
    (show LinearMap.toSpanSingleton R (F → C) (fun a => algebraMap R C (χ a)) 1 ∈
      stepOrder AA.carrier K t from h1)
  have hg0a : ∀ a : F, g0 (a • t) = algebraMap R C (χ a) := by
    intro a
    have := congrFun hg0e a
    simpa [LinearMap.funLeft_apply, LinearMap.toSpanSingleton_apply] using this
  have hg0t : g0 t = 1 := by simpa using hg0a 1
  have hg0z : g0 0 = 0 := by
    have e := hg0a 0
    rwa [zero_smul, MulChar.map_zero, map_zero] at e
  obtain ⟨h, hA, hh⟩ : ∃ h ∈ afFun p (invFun AA.carrier K.toAddSubgroup),
      ¬ v (h t - h 0) < 1 := by
    by_contra hcon
    push Not at hcon
    have key : ∀ φ ∈ Algebra.adjoin R
        ((afFun p (invFun AA.carrier K.toAddSubgroup) : Submodule R (N → C)) : Set (N → C)),
        φ ∈ AA.carrier ∧ v (φ t - φ 0) < 1 := by
      intro φ hφ
      induction hφ using Algebra.adjoin_induction with
      | mem x hx =>
        have hx' := Submodule.mem_inf.1 (SetLike.mem_coe.1 hx)
        exact ⟨(hinv x hx'.1).1, hcon x (SetLike.mem_coe.1 hx)⟩
      | algebraMap r =>
        refine ⟨?_, ?_⟩
        · rw [Algebra.algebraMap_eq_smul_one]
          exact AA.carrier.smul_mem r AA.one_mem
        · simp
      | add x y _ _ hx hy =>
        refine ⟨AA.carrier.add_mem hx.1 hy.1, ?_⟩
        have e : (x + y) t - (x + y) 0 = (x t - x 0) + (y t - y 0) := by
          simp only [Pi.add_apply]
          ring
        rw [e]
        exact v.map_add_lt hx.2 hy.2
      | mul x y _ _ hx hy =>
        refine ⟨AA.mul_mem x y hx.1 hy.1, ?_⟩
        have e : (x * y) t - (x * y) 0 = x t * (y t - y 0) + y 0 * (x t - x 0) := by
          simp only [Pi.mul_apply]
          ring
        rw [e]
        refine v.map_add_lt ?_ ?_
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hle x hx.1 t)) hy.2
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hle y hy.1 0)) hx.2
    have hk := (key g0 ((show invFun AA.carrier K.toAddSubgroup ≤ _ from hGen) hg0)).2
    rw [hg0t, hg0z, sub_zero, map_one] at hk
    exact lt_irrefl _ hk
  have hAi := Submodule.mem_inf.1 hA
  obtain ⟨hM, hK⟩ := hinv h hAi.1
  have hAd := hadd h hAi.2
  obtain ⟨r0, hr0⟩ := hval h hM 0
  have h0p : h 0 ∈ pInt (C := C) R p := by
    have h00 := hAd 0 0
    rw [add_zero, show h 0 - h 0 - h 0 = -h 0 by ring] at h00
    simpa using (pInt (C := C) R p).neg_mem h00
  obtain ⟨h', h'apply, h'M⟩ : ∃ h' : N → C, (∀ x, h' x = h x - h 0) ∧ h' ∈ AA.carrier :=
    ⟨h - r0 • (1 : N → C), fun x => by
      show h x - (r0 • (1 : N → C)) x = h x - h 0
      rw [Pi.smul_apply, Pi.one_apply, Algebra.smul_def, mul_one, hr0],
      AA.carrier.sub_mem hM (AA.carrier.smul_mem r0 AA.one_mem)⟩
  have h'z : h' 0 = 0 := by rw [h'apply, sub_self]
  have h'inv : h' ∈ invFun AA.carrier K.toAddSubgroup :=
    hinvI h' ⟨h'M, fun x k hk => by rw [h'apply, h'apply, hK x k hk]⟩
  have h'add : h' ∈ addFun (C := C) R p N := by
    show ∀ x y, h' (x + y) - h' x - h' y ∈ pInt (C := C) R p
    intro x y
    have e : h' (x + y) - h' x - h' y = (h (x + y) - h x - h y) + h 0 := by
      rw [h'apply, h'apply, h'apply]
      ring
    rw [e]
    exact (pInt (C := C) R p).add_mem (hAd x y) h0p
  have h'af : h' ∈ afFun p AA.carrier := by
    unfold afFun
    exact Submodule.mem_inf.2 ⟨h'M, h'add⟩
  have h'aug : h' ∈ augIdeal AA.carrier := by
    unfold augIdeal
    exact Submodule.mem_inf.2 ⟨h'M, by simp [LinearMap.mem_ker, h'z]⟩
  have h't : ¬ v (h' t) < 1 := by
    rw [h'apply]
    exact hh
  obtain ⟨σ, hσ⟩ := PositivityTheory.HtPt.Rb.fund_ex p C v R hv hp F f hc
  obtain ⟨P1, P2, P3, P4, -⟩ :=
    PositivityTheory.HtPt.Rb.proj_props p C v R hv hp F f hc N AA hFS σ hσ h' h'aug
  obtain ⟨m, -, hm⟩ : ∃ m ∈ Finset.Icc 1 (p ^ f - 1), ¬ v (proj (σ ^ m) h' t) < 1 := by
    by_contra hcon
    push Not at hcon
    apply h't
    rw [P2, Finset.sum_apply]
    exact v.map_sum_lt one_ne_zero hcon
  have hτ : IsFund p (σ ^ m) := by
    by_contra hnf
    have hpf := PositivityTheory.HtPt.Rb.proj_nf p C v R hv hp F f hc N AA hFS h' h'af (σ ^ m) hnf
    exact hm (hpv _ (PositivityTheory.HtPt.Rb.mem_pFun.1 hpf t))
  refine ⟨σ ^ m, hτ, ?_⟩
  have hgE : proj (σ ^ m) h' ∈ AA.carrier ∧ ∀ (a : F) x,
      proj (σ ^ m) h' (a • x) = algebraMap R C ((σ ^ m) a) * proj (σ ^ m) h' x := P1 (σ ^ m)
  have hgI := hinv _ (P4 K h'inv (σ ^ m))
  have hgA : proj (σ ^ m) h' ∈ afFun p AA.carrier := P3 h'af (σ ^ m)
  generalize proj (σ ^ m) h' = g at hgE hgI hgA hm
  obtain ⟨u, hu⟩ := hval g hgE.1 t
  have hvu : v (algebraMap R C u) = 1 := by
    rw [hu]
    exact le_antisymm (hle g hgE.1 t) (not_lt.1 hm)
  have huU : IsUnit u := by
    refine hv.isUnit_of_one (isUnit_iff_ne_zero.2 ?_) hvu
    intro h0
    rw [h0, map_zero] at hvu
    exact zero_ne_one hvu
  have hg0' : g 0 = 0 := by
    have e := hgE.2 0 0
    rwa [zero_smul, MulChar.map_zero, map_zero, zero_mul] at e
  refine (Ideal.eq_top_iff_one _).2 ?_
  show ∃ G ∈ afFun p AA.carrier,
    (∀ (a : F) x, G (a • x) - algebraMap R C ((σ ^ m) a) * G x ∈ pInt (C := C) R p) ∧
    (∀ k ∈ K, G k ∈ pInt (C := C) R p) ∧ G t - algebraMap R C 1 ∈ pInt (C := C) R p
  refine ⟨(↑huU.unit⁻¹ : R) • g, (afFun p AA.carrier).smul_mem _ hgA, ?_, ?_, ?_⟩
  · intro a x
    have e : ((↑huU.unit⁻¹ : R) • g) (a • x) - algebraMap R C ((σ ^ m) a) *
        ((↑huU.unit⁻¹ : R) • g) x = 0 := by
      simp only [Pi.smul_apply, hgE.2 a x, Algebra.smul_def]
      ring
    rw [e]
    exact Submodule.zero_mem _
  · intro k hk
    have hgk : g k = 0 := by
      have e := hgI.2 0 k hk
      rwa [zero_add, hg0'] at e
    simp [hgk]
  · have e : ((↑huU.unit⁻¹ : R) • g) t - algebraMap R C 1 = 0 := by
      rw [Pi.smul_apply, Algebra.smul_def, ← hu, ← map_mul, huU.val_inv_mul, sub_self]
    rw [e]
    exact Submodule.zero_mem _
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderPullbackAlongHomStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_pullback_along_hom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (A' : HopfOrder (C := C) R N') (j : N →+ N'), (∀ g ∈ A'.carrier, (fun x => g (j x)) ∈ AA.carrier) → (∀ g ∈ AA.carrier, (∀ k ∈ j.ker, g k = 0) → g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (j : N → N')) * AA.carrier) → A'.carrier.map (LinearMap.funLeft R C (j : N → N')) = invFun AA.carrier j.ker := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom | exact GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom | (intros; apply GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundle
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V], (∀ Γ : (∀ k, ι k) → AddSubgroup V, IsLatFamily O x Γ → (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) → ∃ E : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧ ∀ E : ChartBundle O (mseg x) N V, IsLatFamily O x E.lat ∧ ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) :=
  @PositivityTheory.Xgn.t_bundle_of_family

end GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectiveSplitModuloElement
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem split_exact_mod : ∀ (A : Type) [CommRing A] [IsDomain A] (P₁ P₂ : Type) [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁] [AddCommGroup P₂] [Module A P₂] [Module.Finite A P₂] [Module.Projective A P₂] (N : ℕ) (a : A) (i : P₁ →ₗ[A] (Fin N → A)) (r : (Fin N → A) →ₗ[A] P₁) (q : (Fin N → A) →ₗ[A] P₂), Module.finrank A P₁ + Module.finrank A P₂ = N → (∀ w, ∃ w', r (i w) = w + a • w') → (∀ y, ∃ x y', y = q x + a • y') → (∀ w, ∃ y, q (i w) = a • y) → ∀ x, (∃ y, q x = a • y) → ∃ w x', x = i w + a • x' :=
  @PositivityTheory.HtPt.Gd.split_exact

end GlobalTheory.CompanionTheory.Ar.HT
end

