module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CuspFlowEqTorusAction
section
set_option autoImplicit false

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate

namespace GlobalTheory.CuspFlow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem herm_comb_eq_zero (X : Data E r) (cu : CuspFD X ρ) (η : Fin ρ → E) :
    herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) = 0 := by
  have h : herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) =
      ∑ a, ∑ b, η a * cc (η b) * herm X.Gm (cu.e a) (cu.e b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, maxCuspsA_vec_apply, cc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    calc ∑ k, ∑ l, ∑ b, ∑ a, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l))
        = ∑ k, ∑ b, ∑ a, ∑ l, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ b, ∑ a, ∑ k, ∑ l, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  rw [h]
  simp [cu.iso]

theorem exists_int_coords (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (η : Fin ρ → E) (hη : (∑ a, η a • cu.e a) ∈ X.Λ) (a : E) (ha : cc a = a)
    (hai : IsIntegral ℤ a) :
    ∃ c : Fin (nZ X ρ) → ℤ, ∑ k, c k • zBas X cu k = ((X.m : E) * a * X.κ0) • mcMη η := by
  obtain ⟨γ, hγ, hγe⟩ := X.transv _ hη (herm_comb_eq_zero X cu η) a ha hai
  have hmem : ((X.m : E) * a * X.κ0) • mcMη η ∈ zGam X cu := by
    refine ⟨fun i j => ?_, γ, hγ, by rw [hγe, maxCuspsA_transv]⟩
    have hk := maxCuspsA_kappa_cc X
    simp only [cc] at hk ha
    simp only [mcMη, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, cc, map_mul, map_natCast,
      hk, ha, IsCMField.complexConj_apply_apply]
    ring
  exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp ((hb.2 _).mp hmem)

theorem exists_linear (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (η : Fin ρ → E) (hη : (∑ a, η a • cu.e a) ∈ X.Λ) :
    ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ),
      (∀ (s : X.Ψ → ℝ) (τ : X.Ψ) (a b : Fin ρ), ∑ k, (L s k : ℂ) * τ.1 (zBas X cu k a b) =
        τ.1 X.κ0 * (s τ : ℂ) * (τ.1 (η a) * conj (τ.1 (η b)))) ∧
      ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  obtain ⟨ω, hω⟩ := FlowMeanContinuity.exists_basis X 0
  have hωp : ∀ j, ω j ∈ X.periods 0 := fun j => by
    have : ω j ∈ RealEmbeddingCharacters.perL X 0 := hω ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  choose a ha hai hae using fun j => (RealEmbeddingCharacters.mem_periods_iff X 0 _).mp (hωp j)
  choose c hc using fun j => exists_int_coords X cu hb η hη (a j) (ha j) (hai j)
  set n0 : ℕ := X.chiOrd 0 with hn0
  have hn0pos : (n0 : ℝ) ≠ 0 := by
    have := RealEmbeddingCharacters.chiOrd_pos X 0
    positivity
  let L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ) := ω.constr ℝ fun j k => (n0 : ℝ) * (c j k : ℝ)
  have hL : ∀ j k, L (ω j) k = (n0 : ℝ) * (c j k : ℝ) := fun j k => by
    simp only [L, Module.Basis.constr_basis]
  refine ⟨L, fun s τ i i' => ?_, fun la p hp k => ?_⟩
  · have hj : ∀ j, ∑ k, (L (ω j) k : ℂ) * τ.1 (zBas X cu k i i') =
        τ.1 X.κ0 * (ω j τ : ℂ) * (τ.1 (η i) * conj (τ.1 (η i'))) := by
      intro j
      have h1 := congrArg (fun M : Matrix (Fin ρ) (Fin ρ) E => τ.1 (M i i')) (hc j)
      simp only [Matrix.sum_apply, Matrix.smul_apply] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, mcMη, Matrix.of_apply,
        smul_eq_mul, zsmul_eq_mul, map_mul, map_intCast, map_natCast,
        Formalism.L2.Pj.FJ.emb_cc'] at h1
      have h2 : (ω j τ : ℂ) = (X.m : ℂ) * (n0 : ℂ) * τ.1 (a j) := by
        rw [hae j, RealEmbeddingCharacters.emb_real (ha j)]
        simp only [RealEmbeddingCharacters.per]
        push_cast
        rfl
      simp only [hL]
      push_cast
      simp only [mul_assoc (n0 : ℂ)]
      rw [← Finset.mul_sum, h1, h2]
      ring
    have hs : s = ∑ j, ω.repr s j • ω j := (ω.sum_repr s).symm
    generalize ω.repr s = t at hs
    subst hs
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc ((t j : ℝ) : ℂ)]
    rw [← Finset.mul_sum, hj]
    ring
  · obtain ⟨b, hb1, hb2, rfl⟩ := (RealEmbeddingCharacters.mem_periods_iff X la p).mp hp
    have h0 : RealEmbeddingCharacters.per X 0 b ∈ Submodule.span ℤ (Set.range ω) := by
      rw [hω]
      exact (RealEmbeddingCharacters.mem_periods_iff X 0 _).mpr ⟨b, hb1, hb2, rfl⟩
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h0
    have h1 : RealEmbeddingCharacters.per X la b =
        ((X.chiOrd la : ℝ) / (n0 : ℝ)) • RealEmbeddingCharacters.per X 0 b := by
      funext τ
      simp only [RealEmbeddingCharacters.per, Pi.smul_apply, smul_eq_mul, ← hn0]
      push_cast
      field_simp
    refine ⟨X.chiOrd la * ∑ j, d j * c j k, ?_⟩
    rw [h1, ← hd]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, map_zsmul, Pi.smul_apply, Finset.sum_apply, hL]
    simp only [smul_eq_mul, zsmul_eq_mul]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp

theorem flow_eq_zAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ η : Fin ρ → E, (∑ a, η a • cu.e a) ∈ X.Λ → ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ), (∀ s x, X.flow (∑ a, η a • cu.e a) (fun τ => (s τ : ℂ)) x = zAct X cu (L s) x) ∧ (∀ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ → ∀ s, ∑ k, phZ X cu χ k * L s k = 2 * ∑ τ : X.Ψ, (τ.1 (hq χ η)).re * s τ) ∧ ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  intro E _ _ _ r ρ X cu hb η hη
  obtain ⟨L, hL, hZ⟩ := exists_linear X cu hb η hη
  refine ⟨L, fun s x => ?_, fun χ _ s => ?_, hZ⟩
  · funext τ
    show X.flowMat (∑ a, η a • cu.e a) τ (s τ : ℂ) * mat x τ =
      zMatC X cu.e τ.1 (∑ k, (L s k : ℂ) • (zBas X cu k).map τ.1) * mat x τ
    rw [maxCuspsA_flowMat, ← TransvectionPeriodicity.emb_kappa]
    congr 2
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mcMηc,
      Matrix.of_apply]
    exact (hL s τ a b).symm
  · simp only [phZ, prE, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hκ : τ.1 X.κ0 ≠ 0 := fun h => by
      have := X.κ0_sign τ
      rw [h] at this
      simp at this
    have key : ∑ k, τ.1 (Matrix.trace (χ.transpose * zBas X cu k) / (X.κ0 / 2)) * (L s k : ℂ) =
        2 * (τ.1 (hq χ η) * (s τ : ℂ)) := by
      have e1 : ∀ k, τ.1 (Matrix.trace (χ.transpose * zBas X cu k) / (X.κ0 / 2)) * (L s k : ℂ) =
          ∑ b, ∑ a, 2 / τ.1 X.κ0 * τ.1 (χ a b) * ((L s k : ℂ) * τ.1 (zBas X cu k a b)) := by
        intro k
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
          map_div₀, map_sum, map_mul, map_ofNat, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
        field_simp
      simp only [e1]
      rw [Finset.sum_comm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hq, map_sum, map_mul, Formalism.L2.Pj.FJ.emb_cc', Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (f := fun a b => 2 * (τ.1 (η a) * τ.1 (χ a b) * conj (τ.1 (η b)) * (s τ : ℂ)))]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.mul_sum, hL]
      field_simp
    have h := congrArg Complex.re key
    simpa [Complex.re_sum] using h

end GlobalTheory.CuspFlow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory

theorem eq_zero_of_forall_smul_mem_countable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Set V}
    (hS : S.Countable) {z : V} (hz : ∀ s : ℂ, s • z ∈ S) : z = 0 := by
  by_contra h
  have hinj : Function.Injective fun s : ℂ => s • z := smul_left_injective ℂ h
  have h1 : (Set.univ : Set ℂ).Countable :=
    (hS.preimage_of_injOn hinj.injOn).mono fun s _ => hz s
  exact not_countable_complex h1

namespace KerPerp

variable {O L Y : Type*} [Ring O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {bar : O → O} {EF : LinearMap.BilinForm ℤ L}

def kerPerp (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')) (y : L →ₗ[O] Y) : Submodule O L where
  carrier := {t | ∀ v, y v = 0 → EF t v = 0}
  zero_mem' v _ := by simp
  add_mem' {t t'} ht ht' v hv := by simp [ht v hv, ht' v hv]
  smul_mem' a t ht v hv := by rw [hadj]; exact ht _ (by simp [hv])

variable {hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')} {y : L →ₗ[O] Y}

theorem mem_kerPerp {t : L} : t ∈ kerPerp hadj y ↔ ∀ v, y v = 0 → EF t v = 0 := Iff.rfl

theorem isotropic (hle : kerPerp hadj y ≤ LinearMap.ker y) {t t' : L} (ht : t ∈ kerPerp hadj y)
    (ht' : t' ∈ kerPerp hadj y) : EF t t' = 0 := ht t' (hle ht')

theorem apply_eq_of_eq {t : L} (ht : t ∈ kerPerp hadj y) {v v' : L} (h : y v = y v') : EF t v = EF t v' := by
  rw [← sub_eq_zero, ← map_sub]
  exact ht _ (by rw [map_sub, h, sub_self])

theorem exists_of_dual (hs : Function.Surjective EF) (φ : Module.Dual ℤ Y) :
    ∃ t ∈ kerPerp hadj y, ∀ v, -EF t v = φ (y v) := by
  obtain ⟨t, ht⟩ := hs (-(φ ∘ₗ y.toAddMonoidHom.toIntLinearMap))
  exact ⟨t, fun v hv => by simp [ht, hv], fun v => by simp [ht]⟩

theorem ker_iff [Module.Projective ℤ Y] (hs : Function.Surjective EF) (v : L) :
    y v = 0 ↔ ∀ t ∈ kerPerp hadj y, EF t v = 0 := by
  refine ⟨fun hv t ht => ht v hv, fun h => (Module.forall_dual_apply_eq_zero_iff ℤ _).1 fun φ => ?_⟩
  obtain ⟨t, ht, hφ⟩ := exists_of_dual (hadj := hadj) (y := y) hs φ
  rw [← hφ, h t ht, neg_zero]

variable (hadj)

def toDual (hy : Function.Surjective y) : kerPerp hadj y →ₗ[ℤ] Module.Dual ℤ Y :=
  LinearMap.mk₂ ℤ (fun t x => -EF t (Function.surjInv hy x))
    (fun _ _ _ => by simp [add_comm]) (fun _ _ _ => by simp)
    (fun t x x' => by
      rw [← neg_add, ← map_add (f := _)]
      exact congrArg _ (apply_eq_of_eq t.2 (by simp [Function.surjInv_eq])))
    (fun k t x => by
      rw [smul_neg, ← map_zsmul]
      exact congrArg _ (apply_eq_of_eq t.2 (by simp [Function.surjInv_eq])))

@[simp] theorem toDual_apply (hy : Function.Surjective y) (t : kerPerp hadj y) (v : L) :
    toDual hadj hy t (y v) = -EF t v :=
  congrArg Neg.neg (apply_eq_of_eq t.2 (Function.surjInv_eq hy _))

theorem toDual_bijective (hb : Function.Bijective EF) (hy : Function.Surjective y) :
    Function.Bijective (toDual hadj hy) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    refine Subtype.ext (hb.1 (LinearMap.ext fun v => ?_))
    have := toDual_apply hadj hy t v
    rw [ht] at this
    simpa using this
  · intro φ
    obtain ⟨t, ht, hφ⟩ := exists_of_dual (hadj := hadj) (y := y) hb.2 φ
    refine ⟨⟨t, ht⟩, LinearMap.ext fun x => ?_⟩
    obtain ⟨v, rfl⟩ := hy x
    rw [toDual_apply, hφ]

def equivDual (hb : Function.Bijective EF) (hy : Function.Surjective y) : kerPerp hadj y ≃ₗ[ℤ] Module.Dual ℤ Y :=
  LinearEquiv.ofBijective _ (toDual_bijective hadj hb hy)

@[simp] theorem equivDual_apply (hb : Function.Bijective EF) (hy : Function.Surjective y) (t : kerPerp hadj y)
    (v : L) : equivDual hadj hb hy t (y v) = -EF t v := toDual_apply hadj hy t v

theorem neg_apply_equivDual_symm (hb : Function.Bijective EF) (hy : Function.Surjective y) (φ : Module.Dual ℤ Y)
    (v : L) : -EF ((equivDual hadj hb hy).symm φ) v = φ (y v) := by
  rw [← equivDual_apply hadj hb hy, LinearEquiv.apply_symm_apply]

theorem equivDual_smul (hb : Function.Bijective EF) (hy : Function.Surjective y) (a : O) (t : kerPerp hadj y)
    (x : Y) : equivDual hadj hb hy (a • t) x = equivDual hadj hb hy t (bar a • x) := by
  obtain ⟨v, rfl⟩ := hy x
  rw [← map_smul y, equivDual_apply, equivDual_apply, Submodule.coe_smul, hadj]

theorem finrank_kerPerp [Module.Free ℤ Y] [Module.Finite ℤ Y] (hb : Function.Bijective EF)
    (hy : Function.Surjective y) : Module.finrank ℤ (kerPerp hadj y) = Module.finrank ℤ Y := by
  rw [(equivDual hadj hb hy).finrank_eq, Module.finrank_linearMap_self]

variable {be : LinearMap.BilinForm ℤ Y}

def nilTo (hb : Function.Bijective EF) (hy : Function.Surjective y)
    (hbe : ∀ (a : O) x x', be (a • x) x' = be x (bar a • x')) : L →ₗ[O] kerPerp hadj y where
  toFun a := (equivDual hadj hb hy).symm (be (y a))
  map_add' a b := by simp
  map_smul' c a := (equivDual hadj hb hy).injective (LinearMap.ext fun x => by
    rw [RingHom.id_apply, equivDual_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_smul, hbe])

theorem neg_apply_nilTo (hb : Function.Bijective EF) (hy : Function.Surjective y)
    (hbe : ∀ (a : O) x x', be (a • x) x' = be x (bar a • x')) (a b : L) :
    -EF (nilTo hadj hb hy hbe a) b = be (y a) (y b) := neg_apply_equivDual_symm hadj hb hy _ b

variable {hadj}

section Nil

variable {nn : L → L}

theorem nil_eq_zero (hi : Function.Injective EF) (h : ∀ a b, -EF (nn a) b = be (y a) (y b)) {a : L}
    (ha : y a = 0) : nn a = 0 :=
  hi (LinearMap.ext fun b => by simpa [ha] using h a b)

end Nil

end KerPerp

namespace AnArc

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem orth_ker_iff (v : A.La) : (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ v.y = 0 ∧ v.l = 0 := by
  constructor
  · intro h
    refine ⟨(Module.forall_dual_apply_eq_zero_iff ℤ _).1 fun φ => ?_, A.Ef_bij.1 (LinearMap.ext fun l => ?_)⟩
    · simpa [EF_apply] using h (La.mk 0 φ.toAddMonoidHom 0) rfl
    · simpa [EF_apply] using h (La.mk 0 0 l) rfl
  · rintro ⟨hy, hl⟩ v' hv'
    simp [EF_apply, hy, hl, hv']

theorem y_l_eq_zero_iff (v : A.La) : v.y = 0 ∧ v.l = 0 ↔ ∃ n, v = La.mk 0 n 0 :=
  ⟨fun h => ⟨v.n, La.ext h.1 rfl h.2⟩, by rintro ⟨n, rfl⟩; exact ⟨rfl, rfl⟩⟩

theorem orth_ker_iff_exists (v : A.La) : (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ ∃ n, v = La.mk 0 n 0 :=
  (A.orth_ker_iff v).trans (A.y_l_eq_zero_iff v)

theorem smul_periodMap_mk_zero_fst_eq_neg_form (s : ℂ) (n : A.X →+ ℤ) (v' : A.La) :
    (s • A.P0 (La.mk 0 n 0)).1 v'.y = -(s * A.EF (La.mk 0 n 0) v') := by
  simp [EF_n_left]

theorem l_eq_zero_of_forall_smul_mem {v : A.La} (hv : v.y = 0) (h : ∀ s : ℂ, (s • A.P0 v).2 ∈ A.abelian₂) : v.l = 0 := by
  have hc : Countable A.abelian₂ := Finsupp.Countable.of_moduleFinite (R := ℤ)
  refine Subtype.ext (eq_zero_of_forall_smul_mem_countable (S := (A.abelian₂ : Set _)) (Set.countable_coe_iff.1 hc) fun s => ?_)
  simpa [hv] using h s

theorem orth_ker_iff_forall_smul_mem (v : A.La) :
    (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ v.y = 0 ∧ ∀ s : ℂ, (s • A.P0 v).2 ∈ A.abelian₂ := by
  rw [orth_ker_iff]
  refine and_congr_right fun hv => ⟨fun hl s => ?_, A.l_eq_zero_of_forall_smul_mem hv⟩
  simp [hv, hl]

theorem smul_periodMap_of_orthogonal_ker {v : A.La} (h : ∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) (s : ℂ) :
    (s • A.P0 v).2 = 0 ∧ ∀ v' : A.La, (s • A.P0 v).1 v'.y = -(s * A.EF v v') := by
  obtain ⟨n, rfl⟩ := (A.orth_ker_iff_exists v).1 h
  exact ⟨by simp, A.smul_periodMap_mk_zero_fst_eq_neg_form s n⟩

theorem nilTo_ne_zero {a : A.La} (ha : a.y ≠ 0) :
    KerPerp.nilTo A.EF_smul A.EF_bijective A.yLin_surjective A.be_adj a ≠ 0 := fun h => by
  have h1 := KerPerp.neg_apply_nilTo A.EF_smul A.EF_bijective A.yLin_surjective A.be_adj a a
  rw [h] at h1
  have h2 : (0 : ℤ) = A.be a.y a.y := by simpa using h1
  exact (A.be_pos _ ha).ne h2

end AnArc

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqSumRingHom
section
namespace GlobalTheory.TraceRealPartConjugateSum

open NumberField

theorem trace_eq_sum_ringHom {E : Type} [Field E] [NumberField E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ => rfl

theorem sum_re_add_conj {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : E) :
    ∑ τ : ↥(ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X),
      Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) =
      (↑((Algebra.trace ℚ E : E → ℚ) x) : ℝ) := by
  classical
  set Ψ := ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X with hΨ
  have hconj : ∀ τ : E →+* ℂ,
      τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = τ x + (ComplexEmbedding.conjugate τ) x := by
    intro τ
    rw [map_add (f := _), ComplexEmbedding.conjugate_coe_eq, ReciprocityTheory.ChartRestriction.G.FD.cc,
      IsCMField.complexEmbedding_complexConj]
  have himg : Ψᶜ = Ψ.image ComplexEmbedding.conjugate := by
    ext τ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      refine ⟨ComplexEmbedding.conjugate τ, ?_, ComplexEmbedding.involutive_conjugate E τ⟩
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E τ]
      exact h
    · rintro ⟨σ, hσ, rfl⟩
      exact (X.cmType σ).1 hσ
  have hsum : ∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = ∑ τ : E →+* ℂ, τ x := by
    rw [← Finset.sum_add_sum_compl Ψ (fun τ : E →+* ℂ => τ x), himg,
      Finset.sum_image (fun a _ b _ h => (ComplexEmbedding.involutive_conjugate E).injective h),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => hconj τ
  calc ∑ τ : ↥Ψ, Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))
      = Complex.re (∑ τ : ↥Ψ, (↑τ : E →+* ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := (Complex.re_sum _ _).symm
    _ = Complex.re (∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := by
      rw [Finset.sum_coe_sort Ψ (fun τ : E →+* ℂ => τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))]
    _ = _ := by
      rw [hsum, ← trace_eq_sum_ringHom x]
      simp

end GlobalTheory.TraceRealPartConjugateSum
end

