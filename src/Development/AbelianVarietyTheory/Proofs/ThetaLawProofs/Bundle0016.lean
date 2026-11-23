module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaLawZeroOfEven
section
namespace GlobalTheory.KeyPow


open Matrix ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem exists_thetaLaw_zero_of_even (hInv : ReciprocityTheory.ChartRestriction.G.Key.Chi.InversionStatement) (g : ℕ)
    (n n' : Fin g → ℤ) (h : Even (n ⬝ᵥ n')) :
    ∃ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, GlobalTheory.KeyPow.ThetaLaw g sp n n' 0 0 := by
  obtain ⟨S, hS, hd⟩ := GlobalTheory.exists_isSymm_mulVec_add_diag_mod_two g n n' h
  have h1 : ThetaLaw g (spTransl S) n n' n 0 :=
    (thetaLaw_generators hInv g n 0).1 S n' hS fun i => by simpa using hd i
  have h2 : ThetaLaw g (Matrix.J (Fin g) ℤ) n 0 0 n := (thetaLaw_generators hInv g 0 n).2
  have hD : (Matrix.diagonal n).IsSymm := Matrix.isSymm_diagonal _
  have h3 : ThetaLaw g (spTransl (Matrix.diagonal n)) 0 n 0 0 :=
    (thetaLaw_generators hInv g 0 0).1 _ n hD fun i => by simp
  have m1 : spTransl S ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hS
  have m2 : Matrix.J (Fin g) ℤ ∈ Matrix.symplecticGroup (Fin g) ℤ := SymplecticGroup.J_mem _ _
  have m3 : spTransl (Matrix.diagonal n) ∈ Matrix.symplecticGroup (Fin g) ℤ := spTransl_mem_sp hD
  exact ⟨_, mul_mem m3 (mul_mem m2 m1), thetaLaw_mul g _ _ _ _ _ _ _ _ m3 (mul_mem m2 m1)
    (thetaLaw_mul g _ _ _ _ _ _ _ _ m2 m1 h1 h2) h3⟩

end GlobalTheory.KeyPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LatticeBlocks
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

theorem det_blocks {j g G : ℕ} {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G)
    (M : Matrix (Fin g) (Fin g) R) :
    (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R).det = M.det ^ j := by
  have h : (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R) =
      Matrix.reindex ((Equiv.prodComm _ _).trans e) ((Equiv.prodComm _ _).trans e)
        (Matrix.blockDiagonal fun _ : Fin j => M) := by
    ext p q
    simp [Matrix.blockDiagonal_apply]
  rw [h, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  simp

theorem lattice_blocks {j g G : ℕ} (e : Fin j × Fin g ≃ Fin G) (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin G → ℂ) :
    (∀ i, ∃ m n : Fin g → ℤ, (fun k => z (e (i, k))) = (fun k => (m k : ℂ)) + τ.mulVec (fun k => (n k : ℂ))) ↔
      ∃ m n : Fin G → ℤ, z = (fun p => (m p : ℂ)) +
        (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
          τ (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) ℂ).mulVec (fun p => (n p : ℂ)) := by
  constructor
  · intro h
    choose m n h using h
    refine ⟨fun p => m (e.symm p).1 (e.symm p).2, fun p => n (e.symm p).1 (e.symm p).2, ?_⟩
    funext p
    obtain ⟨⟨i, k⟩, rfl⟩ := e.surjective p
    have h₁ := congrFun (ThetaPow.mulVec_blocks e τ (fun p => (n (e.symm p).1 (e.symm p).2 : ℂ)) i) k
    have h₂ := congrFun (h i) k
    simp only [Equiv.symm_apply_apply, Pi.add_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]
  · rintro ⟨m, n, rfl⟩ i
    refine ⟨fun k => m (e (i, k)), fun k => n (e (i, k)), ?_⟩
    rw [← ThetaPow.mulVec_blocks e τ (fun p => (n p : ℂ)) i]
    rfl

theorem normalAt_pow : ∀ (x y : KeyIn ℂ) (j : ℕ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℝ) (c : ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → GlobalTheory.KeyPow.NormalAt x τ M (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) c → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (τ' M' : Matrix (Fin y.P.g) (Fin y.P.g) ℂ), M'.det = M.det ^ j ∧ GlobalTheory.KeyPow.NormalAt y τ' M' (fun p => (a (e.symm p).2 : ℂ)) (fun p => (b (e.symm p).2 : ℂ)) (c ^ j) := by
  rintro x y j τ M a b c hp ⟨u, hs, hd, hΛ, hr, hf, hv⟩
  obtain ⟨e, u', hΛ', hr', hf', hv'⟩ := _root_.GlobalTheory.PowUnif.exists_holUnif_pow x y j u _
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M) hp hr hf hv
  obtain ⟨hs', hd', hθ⟩ := thetaChar_blockDiagonal j _ τ a b _ e hs hd
  refine ⟨e, _, _, det_blocks e M, u', hs', hd', fun z => ?_, hr', ?_, fun p => ?_⟩
  · rw [hΛ', ← lattice_blocks]
    exact forall_congr' fun i => hΛ _
  · convert hf' using 2 with z
    rw [hθ, Finset.prod_mul_distrib]
    simp
  · convert hv' p using 1
    funext q
    simp only [Pi.smul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp

end GlobalTheory.KeyPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory
namespace UnifCompare

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

lemma mem_iff (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) (z : Fin g → ℂ) : F z ∈ u₀.Λ ↔ z ∈ u.Λ := by
  rw [← u₀.ker, ← u.ker, hF]

lemma injective (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) : Function.Injective F := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  have hm : ∀ t : ℂ, t • z ∈ u.Λ := fun t => by
    rw [← mem_iff u u₀ F hF, map_smul, hz, smul_zero]
    exact u₀.Λ.zero_mem
  have := u.discrete
  have hc : Continuous fun t : ℂ => (⟨t • z, hm t⟩ : u.Λ) :=
    Continuous.subtype_mk (continuous_id.smul continuous_const) _
  have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hc (x := 1) (y := 0)
  simpa using congrArg Subtype.val h

lemma isDiff_iff (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) (w : Fin g → ℂ) (v : epsR ℂ ⟶ A) :
    u.IsDiff w v ↔ u₀.IsDiff (F w) v := by
  have key : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w =
        fderiv ℂ (fun z => valAt' (u₀.ex z).left U f) 0 (F w) := fun U f => by
    have e : (fun z => valAt' (u.ex z).left U f) = (fun z => valAt' (u₀.ex z).left U f) ∘ F := by
      funext z
      simp only [Function.comp, hF]
    rw [e, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
    rfl
  simp only [HolUnif.IsDiff, key]


open PullHermitian in
lemma hermForm_eq (hL : L.IsLB) (u u₀ : HolUnif A L g) {Hm H₀ : Matrix (Fin g) (Fin g) ℂ}
    {χ : u.Λ → ℂ} {χ₀ : u₀.Λ → ℂ} (hu : u.IsAH Hm χ) (hu₀ : u₀.IsAH H₀ χ₀)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u₀.ex (F z) = u.ex z) (z w : Fin g → ℂ) :
    hermForm H₀ (F z) (F w) = hermForm Hm z w := by
  have hΛ : ∀ l : u.Λ, F l ∈ u₀.Λ := fun l => (mem_iff u u₀ F hF l).2 l.2
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : A.left.Opens} {z}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → ⊤ ≤ (u₀.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun i : L.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (fun i => (u.hol _ 0).1)
    (fun z => exists_chart (u.ex z).left hL)
    (fun i z => u₀.fr i (F z) / u.fr i z)
    (fun i => by
      have d2 := (u₀.fr_hol i).comp (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
        hFd.differentiableOn fun z hz => tr hz
      simp only [div_eq_mul_inv]
      exact d2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have h1 := u.fr_compat i j z (inf_of _ hi hj)
      have h2 := u₀.fr_compat i j (F z) (tr (inf_of _ hi hj))
      rw [hF] at h2
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), h1, h2]
      ring)
  set H₂ := (LinearMap.toMatrix' F).transpose * H₀ * (LinearMap.toMatrix' F).transpose.conjTranspose
    with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hu₀.1
  have hsub : ∀ z w, hermForm (Hm - H₂) z w = hermForm Hm z w - hermForm H₀ (F z) (F w) :=
    fun z w => by
      have := hermForm_sub_smul Hm H₂ 1 1 z w
      rwa [one_smul, one_smul, _root_.one_mul, _root_.one_mul, hH₂, hermForm_pull] at this
  have := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full
    (Hm - H₂) (fun l => χ l / χ₀ ⟨F l, hΛ l⟩) r (hu.1.sub hH₂h)
    (fun l => by simp [hu.2.2.1, hu₀.2.2.1]) hr
    (fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      rw [hrφ i z hi]
      exact div_ne_zero (u₀.fr_ne _ _ (tr hi)) (u.fr_ne _ _ hi))
    (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
      have h1 := hu.2.2.2 l i z hi
      have h2 := hu₀.2.2.2 ⟨F l, hΛ l⟩ i (F z) (tr hi)
      have h3 : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [hu.2.2.1]; exact one_ne_zero)
      have h4 : χ₀ ⟨F l, hΛ l⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hu₀.2.2.1]; exact one_ne_zero)
      have h5 := u.fr_ne _ _ hi'
      rw [hrφ i z hi, hrφ i (z + l) hi']
      simp only [hsub, map_add (f := _)]
      rw [h1, h2]
      simp only [hermForm]
      generalize (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = a
      generalize ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = b
      generalize (F z ⬝ᵥ H₀.mulVec (star (F l))) = a'
      generalize (F l ⬝ᵥ H₀.mulVec (star (F l))) = b'
      have e : Complex.exp (Real.pi * (a - a') + Real.pi / 2 * (b - b')) =
          Complex.exp (Real.pi * a + Real.pi / 2 * b) /
            Complex.exp (Real.pi * a' + Real.pi / 2 * b') := by
        rw [← Complex.exp_sub]
        congr 1
        ring
      have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
      have h7 := Complex.exp_ne_zero (Real.pi * a' + Real.pi / 2 * b')
      rw [e]
      generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
      generalize Complex.exp (Real.pi * a' + Real.pi / 2 * b') = s' at h7
      field_simp)
  have h := hsub z w
  rw [key.1] at h
  have h0 : hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z w = 0 := by simp [hermForm]
  rw [h0] at h
  exact (sub_eq_zero.1 h.symm).symm

end UnifCompare


open UnifCompare in
theorem unimodular_and_tangent_of_isAH :
    ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∀ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    (∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef) ∧
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  intro hT P rig hrig u Hm χ hu
  obtain ⟨u₀, H₀, χ₀, E₀, hu₀, -, hv, hw, -, -, hE, hEb, -⟩ := hT P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g P.g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  have hinj := injective u u₀ F hF
  let e : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofInjectiveEndo F hinj
  have he : ∀ z, e z = F z := fun z => rfl
  have hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v :=
    isDiff_iff u u₀ e.toContinuousLinearEquiv hF
  refine ⟨?_, fun v hv' => ?_, fun w => ?_⟩
  · let φ : u.Λ ≃ₗ[ℤ] u₀.Λ :=
      { toFun := fun a => ⟨e a, (mem_iff u u₀ F hF a).2 a.2⟩
        invFun := fun b => ⟨e.symm b, (mem_iff u u₀ F hF _).1 (by
          rw [← he, e.apply_symm_apply]; exact b.2)⟩
        map_add' := fun a b => Subtype.ext (map_add e a.1 b.1)
        map_smul' := fun n a => Subtype.ext (map_zsmul e n a.1)
        left_inv := fun a => Subtype.ext (e.symm_apply_apply a.1)
        right_inv := fun b => Subtype.ext (e.apply_symm_apply b.1) }
    refine ⟨φ.dualMap.toLinearMap ∘ₗ E₀ ∘ₗ φ.toLinearMap, fun a b => ?_,
      φ.dualMap.bijective.comp (hEb.comp φ.bijective)⟩
    rw [← hermForm_eq P.isLB u u₀ hu hu₀ F hF]
    exact hE (φ a) (φ b)
  · obtain ⟨w, h1, h2⟩ := hv v hv'
    refine ⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩
    rw [← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]
  · simp only [hd]
    exact hw (e w)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

section Scale

variable {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X}

theorem res_constFn {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a :=
  congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

theorem constFn_mul (U : X.Opens) (a b : R) : constFn p U (a * b) = constFn p U a * constFn p U b := by
  rw [constFn, constFn, constFn, map_mul, map_mul]

theorem constFn_one (U : X.Opens) : constFn p U (1 : R) = 1 := by
  rw [constFn, map_one, map_one]

theorem exists_sec_div {a b : R} (h : a * b = 1) (s : L.Sec) :
    ∃ t : L.Sec, (∀ i, t.f i = constFn p _ b * s.f i) ∧ (∀ i, s.f i = constFn p _ a * t.f i) ∧
      Out.nonzeroLocus s ≤ Out.nonzeroLocus t := by
  have e : ∀ i, s.f i = constFn p _ a * (constFn p _ b * s.f i) := fun i => by
    rw [← _root_.mul_assoc, ← constFn_mul, h, constFn_one, _root_.one_mul]
  refine ⟨⟨fun i => constFn p _ b * s.f i, fun i j => ?_⟩, fun _ => rfl, e, iSup_mono fun i => ?_⟩
  · rw [map_mul, map_mul, res_constFn, res_constFn, s.compat i j, mul_left_comm]
  · conv_lhs => rw [e i, Scheme.basicOpen_mul]
    exact inf_le_right

end Scale

theorem value_at_normalForm :
    ∀ (N : ℕ → ℕ) (g₀ : ℕ) (κ : KeyIn ℂ → ℂˣ) (g : ℕ) (a b : Fin g → ℂ), g₀ ≤ g → GlobalTheory.KeyPow.ClauseH ℂ N g₀ κ → (∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 → κ x = 1) → ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ), c ≠ 0 → M.det ≠ 0 → GlobalTheory.KeyPow.NormalAt x τ M (fun i => a (i.cast h)) (fun i => b (i.cast h)) c → (κ x : ℂ) = (M.det ^ 4 / c ^ 8) ^ N g := by
  intro N g₀ κ g a b hg₀ hH hN x h τ M c hc hM hx
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  dsimp only at h τ M
  subst h
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hx
  haveI := P.isAb.comm
  obtain ⟨ex, tan, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v hv.1
  choose v₀ hv₀ using fun i => (ex (M⁻¹ i)).exists
  have hb₀ : IsLieBasis v₀ := (bas M⁻¹ v₀ hv hv₀).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit)
  obtain ⟨ex₀, -, -, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v₀ hb₀.1
  have hMv : ∀ i, IsLieComb (M i) v₀ (v i) := fun i => by
    obtain ⟨w, hw⟩ := (ex₀ (M i)).exists
    have h1 := comp _ (fun i => M⁻¹ i) v₀ (M i) w hv₀ hw
    have e : ∑ j, M i j • M⁻¹ j = Pi.single i 1 := by
      rw [← Matrix.vecMul_eq_sum]
      refine (congrFun (Matrix.mul_nonsing_inv M hM.isUnit) i).trans ?_
      simpa using smul_one_row (1 : ℂ) i
    rw [e] at h1
    rwa [(ex _).unique (sgl i) h1]
  obtain ⟨th₀, e₀, e₁, hle⟩ := exists_sec_div P.A.hom (mul_inv_cancel₀ hc) th
  have hth₀ : ∀ s : Sp ℂ, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀ :=
    fun s => (hth s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  have h0 : κ ⟨P, hg, rig, hr, th₀, hth₀, v₀, hb₀⟩ = 1 := by
    refine hN ⟨P, hg, rig, hr, th₀, hth₀, v₀, hb₀⟩ rfl τ ⟨u, h₁, h₂, h₃, h₄, ?_, ?_⟩
    · intro i z hz
      have e := h₅ i z hz
      refine ((congrArg (valAt' _ _) (e₀ i)).trans (valAt'_mul _ _ _ _)).trans ?_
      rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
      refine (congrArg (c⁻¹ * ·) e).trans ?_
      beta_reduce
      rw [_root_.one_mul, ← _root_.mul_assoc, inv_mul_cancel_left₀ hc]
    · intro i
      have h1 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 h₆ (hv₀ i)
      have e : ∑ j, M⁻¹ i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin P.g) (Fin P.g) ℂ) i := by
        simp only [smul_comm (M⁻¹ i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
        rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum, ← Matrix.nonsing_inv_mul M hM.isUnit]
        rfl
      rwa [e] at h1
  have h1 := hH P hg rig hr _ hth₀ v₀ hb₀ th hth v hv c M hg₀ e₁ hMv
  rw [h0, Units.val_one, _root_.mul_one] at h1
  rw [div_pow, ← pow_mul, ← pow_mul, eq_div_iff (pow_ne_zero _ hc), mul_comm]
  exact h1

end GlobalTheory.KeyPow
end
end

