module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.ThetaOnto

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  unfold constFn
  rw [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_map]

theorem constFn_zero {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero]

def secComb {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {K : Type}
    [Fintype K] (a : K → R) (s : K → L.Sec) : L.Sec where
  f j := ∑ i, constFn p _ (a i) * (s i).f j
  compat j k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (s i).compat j k]
    ring

def secConst {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (L : LB X) (a : R) :
    (lbPow L 0).Sec where
  f j := constFn p _ a
  compat j k := by
    have : (lbPow L 0).g j k = 1 := by
      unfold lbPow LB.LinComb
      dsimp only
      exact Finset.prod_eq_one fun _ _ => zpow_zero _
    rw [res_constFn, res_constFn, this, Units.val_one, _root_.one_mul]

theorem mem_span_of_card_le {V : Type} [AddCommGroup V] [Module ℂ V] (Q : V → Prop) {N : ℕ}
    (hN : ∀ (M : ℕ) (f : Fin M → V), (∀ k, Q (f k)) → LinearIndependent ℂ f → M ≤ N)
    (f : Fin N → V) (hf : ∀ k, Q (f k)) (hli : LinearIndependent ℂ f) {v : V} (hv : Q v) :
    ∃ a : Fin N → ℂ, ∑ i, a i • f i = v := by
  by_contra hne
  have hv' : v ∉ Submodule.span ℂ (Set.range f) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact hne
  have hli' : LinearIndependent ℂ (Fin.cons v f : Fin (N + 1) → V) :=
    linearIndependent_finCons.mpr ⟨hli, hv'⟩
  have hQ : ∀ k, Q ((Fin.cons v f : Fin (N + 1) → V) k) := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hv
    · simpa using hf i
  have := hN (N + 1) _ hQ hli'
  omega

theorem theta_from_section :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, Differentiable ℂ (f k) ∧ ∀ (l : Λ) z, f k (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f k z) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (P : Out.PolAV (Sp ℂ)) (n : ℕ), 1 ≤ n → ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ, (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ → (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → ∀ (n : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ) := by
  intro hval hdim hsec hfun P u Hm χ Ef hAH hfr hEf n θ hθ
  have hpt : ∀ z, (u.ex z).left ≫ P.A.hom = 𝟙 _ := fun z => Over.w (u.ex z)
  have hconst : ∀ z (U : P.A.left.Opens) (a : ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ U →
      valAt' (u.ex z).left U (constFn P.A.hom U a) = a :=
    fun z U a hU => (hval _ _).2.2.2.2.2 P.A.hom (hpt z) U a hU
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    have hper : ∀ (l : u.Λ) z, θ (z + l) = θ z := fun l z => by
      rw [hθ.2 l z, pow_zero, _root_.one_mul]
    have := u.discrete
    have : IsZLattice ℝ u.Λ := ⟨u.full⟩
    let b := (Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ
    have hb : Bornology.IsBounded (Set.range θ) := by
      have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
        Metric.isCompact_of_isClosed_isBounded isClosed_closure
          (ZSpan.fundamentalDomain_isBounded b).closure
      refine (hK.image hθ.1.continuous).isBounded.subset ?_
      rintro _ ⟨z, rfl⟩
      refine ⟨ZSpan.fract b z, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), ?_⟩
      have hfl : ((ZSpan.floor b z : _) : Fin P.g → ℂ) ∈ u.Λ := by
        have h : ((ZSpan.floor b z : _) : Fin P.g → ℂ) ∈ Submodule.span ℤ (Set.range b) :=
          (ZSpan.floor b z).2
        exact ((Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis_span ℝ).le h
      rw [← hper ⟨_, hfl⟩ (ZSpan.fract b z), ZSpan.fract_apply, sub_add_cancel]
    have hc : ∀ z, θ z = θ 0 := fun z => hθ.1.apply_eq_apply_of_bounded hb z 0
    refine ⟨secConst P.A.hom P.L (θ 0), ?_⟩
    intro j z hz
    show valAt' _ _ (constFn P.A.hom _ (θ 0)) = _
    rw [hconst z _ _ hz, pow_zero, _root_.mul_one, hc z]
  ·
    obtain ⟨s, hs⟩ := hsec P n hn
    have hex : ∀ i, ∃ T, u.IsThetaFn Hm χ n T ∧ u.IsFnPow n (s i) T :=
      fun i => ((hfun P u Hm χ Ef hfr n).1 (s i)).exists
    choose T hT using hex
    have hcomb : ∀ a : Fin (n ^ P.g) → ℂ,
        u.IsFnPow n (secComb P.A.hom a s) (fun z => ∑ i, a i * T i z) := by
      intro a j z hz
      obtain ⟨e, he⟩ := (hval _ (u.ex z).left).2.1 _ hz
      have hca : ∀ i, e (constFn P.A.hom ((lbPow P.L n).U j) (a i)) = a i := fun i => by
        rw [← he]; exact hconst z _ (a i) hz
      have hsi : ∀ i, e ((s i).f j) = T i z * u.fr (j PUnit.unit) z ^ n := fun i => by
        rw [← he]; exact (hT i).2 j z hz
      rw [he]
      show e (∑ i, constFn P.A.hom _ (a i) * (s i).f j) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hca, hsi, _root_.mul_assoc]
    have hli : LinearIndependent ℂ T := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hz : ∀ z, ∑ i, a i * T i z = 0 := fun z => by
        simpa [Finset.sum_apply] using congrFun ha z
      have h0 : u.IsFnPow n (secComb P.A.hom (0 : Fin (n ^ P.g) → ℂ) s)
          (fun z => ∑ i, a i * T i z) := by
        intro j z hz'
        rw [hcomb 0 j z hz']
        simp [hz]
      have heq := (hfun P u Hm χ Ef hfr n).2 _ _ _ (hcomb a) h0
      have ha0 : a = 0 := by
        apply hs a
        intro j
        have hj := congrArg (fun t => LB.Sec.f t j) heq
        simp only [secComb] at hj
        rw [hj]
        simp [constFn_zero]
      intro i
      rw [ha0]
      rfl
    obtain ⟨a, ha⟩ := mem_span_of_card_le (u.IsThetaFn Hm χ n)
      (fun M f hf hlin => hdim P.g u.Λ u.discrete u.full Hm χ Ef hfr.1 hAH.2.1 hfr.2.1 hfr.2.2.1 hEf
        n hn M f (fun k => ⟨(hf k).1, fun l z => (hf k).2 l z⟩) hlin)
      T (fun i => (hT i).1) hli hθ
    refine ⟨secComb P.A.hom a s, ?_⟩
    intro j z hz
    rw [hcomb a j z hz, ← ha]
    simp [Finset.sum_apply]

end GlobalTheory.ThetaOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

section
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem holUnif_ex_zero_eq_one : u.ex 0 = 1 :=
  (u.ker 0).2 (zero_mem _)

theorem holUnif_ex_nsmul_eq_pow (z : Fin g → ℂ) (k : ℕ) : u.ex (k • z) = u.ex z ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem holUnif_isZLattice : haveI := u.discrete; IsZLattice ℝ u.Λ := by
  have := u.discrete
  exact ⟨u.full⟩

end

theorem riemannForm_bijective_of_weilNondeg :
    Out.WeilNondegSt → (∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (E : LinearMap.BilinForm ℤ X), (∀ (k : ℕ) (a : X), 0 < k → (∀ b, (k : ℤ) ∣ E a b) → ∃ a', a = (k : ℤ) • a') → Function.Bijective E) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c)) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef) := by
  intro hW hB hE P u Hm χ Ef hc
  have := u.discrete
  have := holUnif_isZLattice u
  apply hB u.Λ Ef
  intro k a hk hdiv
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'

  have hpow : ∀ w : Fin P.g → ℂ, u.ex w ^ k = u.ex ((k : ℂ) • w) := by
    intro w
    rw [← holUnif_ex_nsmul_eq_pow, Nat.cast_smul_eq_nsmul]
  have hx : u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) = 1 := by
    refine hW ℂ P k hk0 _ ?_ ?_
    · rw [hpow, smul_smul, mul_inv_cancel₀ hk0, one_smul]
      exact (u.ker _).2 a.2
    · intro y hy
      obtain ⟨w, rfl⟩ := u.ex_onto y
      have hw : (k : ℂ) • w ∈ u.Λ := (u.ker _).1 (by rw [← hpow]; exact hy)
      set b : u.Λ := ⟨(k : ℂ) • w, hw⟩
      have hwb : w = (k : ℂ)⁻¹ • (b : Fin P.g → ℂ) := by
        simp only [b, smul_smul, inv_mul_cancel₀ hk0, one_smul]
      obtain ⟨m, hm⟩ := hdiv b
      have h1 := hE P u Hm χ Ef hc k a b 1 hk (by
        rw [hm, Units.val_one]
        push_cast
        rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((k : ℂ) * (m : ℂ)) / (k : ℂ)
            = (-m : ℤ) * (2 * Real.pi * Complex.I) by push_cast; field_simp]
        exact (Complex.exp_int_mul_two_pi_mul_I (-m)).symm)
      have hu : unitOn (1 : ℂˣ) = 1 := map_one _
      rw [hu, ← hwb] at h1
      exact h1
  refine ⟨⟨(k : ℂ)⁻¹ • (a : Fin P.g → ℂ), (u.ker _).1 hx⟩, ?_⟩
  ext1
  simp only [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast, smul_smul,
    mul_inv_cancel₀ hk0, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.SectionTheta

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem ex_add_lattice (u : HolUnif A L g) (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem quot_eq (u : HolUnif A L g) (z : Fin g → ℂ)
    (hhom : ∀ U : A.left.Opens, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U →
      ∃ e : Γ(A.left, U) →+* ℂ, ∀ f, valAt' (u.ex z).left U f = e f)
    (hres : ∀ (U V : A.left.Opens) (h : V ≤ U) (f : Γ(A.left, U)), ⊤ ≤ (u.ex z).left ⁻¹ᵁ V →
      valAt' (u.ex z).left V (resG A.left h f) = valAt' (u.ex z).left U f)
    (n : ℕ) (s : (lbPow L n).Sec) (j j' : (lbPow L n).ι)
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j) (hj' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j') :
    valAt' (u.ex z).left ((lbPow L n).U j) (s.f j) / u.fr (j PUnit.unit) z ^ n =
      valAt' (u.ex z).left ((lbPow L n).U j') (s.f j') / u.fr (j' PUnit.unit) z ^ n := by
  have hW : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((lbPow L n).U j ⊓ (lbPow L n).U j') :=
    fun p hp => ⟨hj hp, hj' hp⟩
  have hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit) := Cartier.lbPow_U L n j ▸ hj
  have hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j' PUnit.unit) := Cartier.lbPow_U L n j' ▸ hj'
  have hW' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
    fun p hp => ⟨hi hp, hi' hp⟩
  obtain ⟨e, he⟩ := hhom _ hW
  have h1 := hres _ _ (inf_le_left : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j) hW
  have h2 := hres _ _ (inf_le_right : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j') hW
  have h3 := hres _ _ (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le)
    (L.g (j PUnit.unit) (j' PUnit.unit)).val hW
  have hc : resG A.left (inf_le_left : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j) =
      (resG A.left (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le)
        (L.g (j PUnit.unit) (j' PUnit.unit)).val) ^ n *
      resG A.left (inf_le_right : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j') := by
    refine (s.compat j j').trans ?_
    exact congrArg (· * _) ((congrArg Units.val (Cartier.lbPow_g L n j j')).trans
      (Units.val_pow_eq_pow_val _ _))
  have hfr := u.fr_compat _ _ z hW'
  have hne := u.fr_ne _ z hi
  have hne' := u.fr_ne _ z hi'
  rw [← h1, ← h2, hc, he, map_mul, map_pow, ← he, ← he, h3]
  rw [hfr] at hne ⊢
  have hg := left_ne_zero_of_mul hne
  rw [mul_pow]
  field_simp

end GlobalTheory.SectionTheta

namespace GlobalTheory

open SectionTheta

theorem sections_pow_theta_functions :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), Smooth p → IsReduced X) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') := by
  intro hval hext hred P u Hm χ Ef hAH n
  obtain ⟨-, -, -, hlaw⟩ := hAH
  have hcov : ∀ z, ∃ j : (lbPow P.L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L n).U j := by
    intro z
    have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, P.L.U i := by
      rw [P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    refine ⟨fun _ => i, ?_⟩
    rw [Cartier.lbPow_U]
    exact ((hval _ (u.ex z).left).1 _).2 hi
  have hU : ∀ z (j : (lbPow P.L n).ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L n).U j →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j PUnit.unit) := fun z j hj => Cartier.lbPow_U P.L n j ▸ hj
  refine ⟨fun s => ?_, fun θ s s' hs hs' => ?_⟩
  · choose c hc using hcov
    let θ : (Fin P.g → ℂ) → ℂ := fun z =>
      valAt' (u.ex z).left ((lbPow P.L n).U (c z)) (s.f (c z)) / u.fr (c z PUnit.unit) z ^ n
    have hθ : ∀ (j : (lbPow P.L n).ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L n).U j →
        θ z = valAt' (u.ex z).left ((lbPow P.L n).U j) (s.f j) / u.fr (j PUnit.unit) z ^ n :=
      fun j z hj => quot_eq u z (hval _ _).2.1 (hval _ _).2.2.1 n s _ _ (hc z) hj
    have hfn : u.IsFnPow n s θ := by
      intro j z hj
      rw [hθ j z hj, div_mul_cancel₀ _ (pow_ne_zero n (u.fr_ne _ z (hU z j hj)))]
    refine ⟨θ, ⟨⟨fun z => ?_, fun l z => ?_⟩, hfn⟩, fun θ' hθ' => ?_⟩
    · obtain ⟨ho, hd⟩ := u.hol _ (s.f (c z))
      have hn := ho.mem_nhds (hc z)
      have hd2 : DifferentiableOn ℂ (u.fr (c z PUnit.unit))
          {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (lbPow P.L n).U (c z)} :=
        (u.fr_hol _).mono fun w hw => hU w _ hw
      have hq := (hd.differentiableAt hn).mul (((hd2.differentiableAt hn).pow n).inv
        (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))))
      refine hq.congr_of_eventuallyEq ?_
      filter_upwards [hn] with w hw
      exact (hθ _ w hw).trans (div_eq_mul_inv _ _)
    · have h1 := hfn (c z) z (hc z)
      have hc' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ (lbPow P.L n).U (c z) := by
        rw [ex_add_lattice]; exact hc z
      have h2 := hfn (c z) (z + l) hc'
      rw [ex_add_lattice, h1, hlaw l _ z (hU z _ (hc z)), mul_pow, ← _root_.mul_assoc] at h2
      have h3 := mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ _ (hU _ _ hc'))) h2
      rw [← h3, _root_.mul_comm]
      rfl
    · funext z
      have h1 := hfn (c z) z (hc z)
      rw [hθ'.2 (c z) z (hc z)] at h1
      exact mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))) h1
  · have hsm : Smooth P.A.hom := by
      have := P.smoothDim
      exact SmoothOfRelativeDimension.smooth P.g P.A.hom
    have hf : s.f = s'.f := by
      funext j
      refine hext P.A (hred _ _ hsm) inferInstance _ _ _ fun x hx => ?_
      obtain ⟨z, rfl⟩ := u.ex_onto x
      rw [hs j z hx, hs' j z hx]
    cases s
    cases s'
    cases hf
    rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfParts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem thetaUnifAV_of_parts :
    (∀ P : Out.PolAV (Sp ℂ), ∃ u : HolUnif P.A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
        : LB P.A.left) P.g, (∃ (U : P.A.left.Opens) (t : Fin P.g → Γ(P.A.left,
        U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(P.A.left, U) →+ ℂ, (∀ a, D (constFn
        P.A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex
        0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex
        w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin P.g → ℂ)) 0) ∧ (∀ (n : ℕ) (a : (Fin n →
        ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), (∀ (U : (P.A).left.Opens) (f : Γ((P.A).left, U)), IsOpen {w
        | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ (Set.univ
        : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 → ∃ G : (Fin n → ℂ) → (Fin P.g →
        ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, u.ex (G w) = a w)) → (∀ (A : Over (Sp
        ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∃ (U : A.left.Opens) (t
        : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left,
        U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex
        0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t
        i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t
        i)) (ContinuousLinearMap.id ℂ (Fin g →
        ℂ)) 0) → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) → (∀ (A
        : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∀ (n : ℕ) (a : (Fin
        n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : (A).left.Opens) (f : Γ((A).left, U)), IsOpen {w
        | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ (Set.univ
        : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 → ∃ G : (Fin n → ℂ) → (Fin g →
        ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, u.ex (G
        w) = a w) → ∀ f : A ⟶ A, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F
        z) = u.ex z ≫ f) → (∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec
        P.A))), rig.IsGen → ∀ u₀ : HolUnif P.A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
        : LB P.A.left) P.g, ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ
        : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), u.ex = u₀.ex ∧ u.IsRig rig ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef
        l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) → (∀ (P : Out.PolAV (Sp ℂ)) (u
        : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c
        : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) /
        k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b
        : Fin P.g → ℂ))) (unitOn c)) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm
        : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef) → (∀ (P : Out.PolAV (Sp ℂ)) (u
        : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z +
        l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P
        : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ
        : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ → (Hm.IsHermitian ∧
        (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m
        : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l *
        cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ)
        ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → ∀ (n
        : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ) → (∀ (P : Out.PolAV (Sp ℂ)) (u
        : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z +
        l)) → Function.Bijective Ef → u.IsAH Hm χ) → ThetaUnifAV := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 P rig hrig
  obtain ⟨u₀, hco, hlift⟩ := h1 P
  obtain ⟨u, Hm, χ, Ef, hex, hr, hd⟩ := h4 P rig hrig u₀
  rw [← hex] at hco hlift
  have hb := h6 P u Hm χ Ef hd
  have hAH := h9 P u Hm χ Ef hd hb
  have ht := h2 P.A P.L P.g u hco
  refine ⟨u, Hm, χ, Ef, hAH, hr, ht.1, ht.2, h3 P.A P.L P.g u hlift, fun n => ⟨(h7 P u Hm χ Ef hd n).1, fun θ hθ => ?_⟩,
    hd.2.2.1, hb, h5 P u Hm χ Ef hd⟩
  obtain ⟨s, hs⟩ := h8 P u Hm χ Ef hAH hd hb n θ hθ
  exact ⟨s, hs, fun s' hs' => (h7 P u Hm χ Ef hd n).2 θ s' s hs' hs⟩

end GlobalTheory
end

