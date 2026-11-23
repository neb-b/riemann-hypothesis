module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABHasDerivAtY
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorKernelMemMapIdeal
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensor_kernel_mem_map_ideal : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [Module.Flat P L] (I : Ideal P),
    RingHom.ker (algebraMap P T) = I → ∀ y : L, (1 : T) ⊗ₜ[P] y = 0 → y ∈ I.map (algebraMap P L) := by
  first | (exact @GlobalTheory.flat_one_tmul_eq_zero_mem_map) | (exact GlobalTheory.flat_one_tmul_eq_zero_mem_map) | (intros; apply GlobalTheory.flat_one_tmul_eq_zero_mem_map  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def fullRankSB (a d : ℕ) : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ) where
  carrier := {Ψ | Ψ ∈ SB (Matrix (Fin a) (Fin d) k) ∧ ∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0}
  zero_mem' := ⟨(SB _).zero_mem, fun _ _ => rfl⟩
  add_mem' := fun hΦ hΨ => ⟨(SB _).add_mem hΦ.1 hΨ.1, fun Y hY => by simp [hΦ.2 Y hY, hΨ.2 Y hY]⟩
  smul_mem' := fun c Φ hΦ => ⟨(SB _).smul_mem c hΦ.1, fun Y hY => by simp [hΦ.2 Y hY]⟩

def coinv (ν β : kˣ →* ℂˣ) (a d : ℕ) : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
    Ψ ∈ SB (Matrix (Fin a) (Fin d) k) ∧ z = omA ν β g 1 Ψ - Ψ}

abbrev blocks (a b : ℕ) : (Σ x, Two (Fin a) (Fin b) x) ≃ Fin (a + b) := two (stdSum (rfl : a + b = a + b))

def parChar (ν β : kˣ →* ℂˣ) (a b : ℕ) : parab k (blocks a b) →* ℂˣ :=
  (deltaHalf k (Two (Fin a) (Fin b)) * ((detChar (Fin a) (ν * β)).comp (MonoidHom.fst _ _)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom *
    ((detChar (Fin b) β).comp (MonoidHom.snd _ _)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom).comp
    (leviProj k (blocks a b))

def indScal (ν β : kˣ →* ℂˣ) (a b : ℕ) : Submodule ℂ (GL (Fin (a + b)) k → ℂ) :=
  smoothPart (rightReg ℂ (GL (Fin (a + b)) k) ℂ) ⊓ indSpace (parab k (blocks a b)) (ofChar (parChar ν β a b))

variable [MeasurableSpace k] [BorelSpace k]

def fibre (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (x : GL (Fin (a + b)) k) : ℂ :=
  ∫ g : GL (Fin a) k, omA ν β 1 x Φ (g.val * X0 (k := k) finSumFinEquiv) * (ν (gdet g) : ℂ) *
    apow (gdet g) (((a + b : ℕ) : ℂ) / 2) ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))

theorem fibre_omA (ν β : kˣ →* ℂˣ) (a b : ℕ) (h : GL (Fin (a + b)) k) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (x : GL (Fin (a + b)) k) : fibre ν β a b (omA ν β 1 h Φ) x = fibre ν β a b Φ (x * h) := by
  unfold fibre
  congr 1
  funext g
  rw [← omA_mul, one_mul]

end GlobalTheory.RankFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
section
noncomputable section

open GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lact {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ) :
    Matrix (Fin n) (Fin d) k → ℂ :=
  fun Y => (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2) * Ψ ((g.1)ᵀ * Y)


variable (k) in
def fullRk (n d : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) where
  carrier := {Ψ | Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) ∧ ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ Y = 0}
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => rfl⟩
  add_mem' := fun ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun Y hY => by simp [ha.2 Y hY, hb.2 Y hY]⟩
  smul_mem' := fun c _ ha => ⟨Submodule.smul_mem _ c ha.1, fun Y hY => by simp [ha.2 Y hY]⟩

def augRk (n d : ℕ) (ν : kˣ →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ g : GL (Fin n) k, ∃ Ψ ∈ fullRk k n d, z = lact ν g Ψ - Ψ}


variable (k) in
def Y0 (n d : ℕ) : Matrix (Fin n) (Fin d) k := Matrix.of fun i j => if (j : ℕ) = d - n + i then 1 else 0


variable (k) in
def indSp (n d : ℕ) (ν : kˣ →* ℂˣ) : Submodule ℂ (GL (Fin d) k → ℂ) where
  carrier := {f | (∃ U ∈ nhds (1 : GL (Fin d) k), ∀ h, ∀ u ∈ U, f (h * u) = f h) ∧
    ∀ (b h : GL (Fin d) k) (D : GL (Fin n) k), Y0 k n d * b.1 = D.1 * Y0 k n d →
      f (b * h) = (((ν (gdet D))⁻¹ : ℂˣ) : ℂ) * apow (gdet D) (-(d : ℂ) / 2) * f h}
  zero_mem' := ⟨⟨Set.univ, Filter.univ_mem, fun _ _ _ => rfl⟩, fun _ _ _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨⟨U, hU, hf⟩, hf'⟩ ⟨⟨V, hV, hg⟩, hg'⟩
    refine ⟨⟨U ∩ V, Filter.inter_mem hU hV, fun h u hu => ?_⟩, fun b h D hD => ?_⟩
    · simp [hf h u hu.1, hg h u hu.2]
    · simp [hf' b h D hD, hg' b h D hD, mul_add]
  smul_mem' := by
    rintro c f ⟨⟨U, hU, hf⟩, hf'⟩
    refine ⟨⟨U, hU, fun h u hu => ?_⟩, fun b h D hD => ?_⟩
    · simp [hf h u hu]
    · simp [hf' b h D hD]; ring

end GlobalTheory.FullRankCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.G2AddWeierstrassPRowSumStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.G2_add_weierstrassP_row_sum : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 2) (EisensteinSeries.G2 τ + (tauPair τ).weierstrassP z) := by
  first | exact @GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP | exact GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP | (intros; apply GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseFlatNoetherianIntClosed
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleBase

theorem flat_noetherian_nzd_intClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    Module.Flat A (Localization.AtPrime QA) ∧ IsNoetherianRing (Localization.AtPrime QA) ∧
      algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X ∈ nonZeroDivisors (Localization.AtPrime QA) ∧
      ∀ f : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA), IsIntegral (Localization.AtPrime QA) f →
        ∃ r : Localization.AtPrime QA, algebraMap _ (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) r = f := by
  intro A _ _ _ _ _ _ EA _ _ _ _ _ QA _ _ ρ _ _
  set R := Localization.AtPrime QA
  haveI : Algebra.Smooth A (Polynomial A) := Algebra.Smooth.mk
  haveI : Algebra.Smooth A EA := Algebra.Smooth.comp A (Polynomial A) EA
  haveI : Module.Flat EA R := IsLocalization.flat R QA.primeCompl
  haveI : Module.Flat A EA := Algebra.Smooth.flat A EA
  haveI : Module.Flat (Polynomial A) EA := Algebra.Smooth.flat (Polynomial A) EA
  have hflat : Module.Flat A R := Module.Flat.trans A EA R
  refine ⟨hflat, ?_, ?_, ?_⟩
  · haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
    exact IsLocalization.isNoetherianRing QA.primeCompl R inferInstance
  · haveI : Module.Flat (Polynomial A) R := Module.Flat.trans (Polynomial A) EA R
    have hX : (Polynomial.X : Polynomial A) ∈ nonZeroDivisors (Polynomial A) :=
      Polynomial.monic_X.mem_nonZeroDivisors
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hX
    have h1 : ∀ z : R, algebraMap (Polynomial A) R Polynomial.X * z = 0 → z = 0 := by
      intro z hz
      apply hreg
      simp only [Algebra.smul_def, smul_zero, mul_zero]
      exact hz
    exact ⟨h1, fun z hz => h1 z (by rw [mul_comm]; exact hz)⟩
  · intro f hf
    set K := FractionRing A
    letI : Algebra K (R ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
    haveI : IsScalarTower A K (R ⊗[A] K) := inferInstance
    haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (R ⊗[A] K) :=
      (Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) K).2 inferInstance
    let e : GlobalTheory.LocAcyc.GenFib A R ≃ₐ[R] R ⊗[A] K :=
      IsLocalization.algEquiv (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) _ _
    have H1 : Function.Bijective (TensorProduct.toIntegralClosure A EA K) :=
      TensorProduct.toIntegralClosure_bijective_of_smooth
    have H2 : Function.Bijective (TensorProduct.toIntegralClosure EA R (EA ⊗[A] K)) :=
      TensorProduct.toIntegralClosure_bijective_of_isLocalization QA.primeCompl
    have H : Function.Bijective (TensorProduct.toIntegralClosure A R K) :=
      TensorProduct.toIntegralClosure_bijective_of_tower H1 H2
    have hf' : IsIntegral R (e f) := hf.map e.toAlgHom
    obtain ⟨y, hy⟩ := H.2 ⟨e f, hf'⟩
    have hy' : (TensorProduct.toIntegralClosure A R K y : R ⊗[A] K) = e f := congrArg Subtype.val hy
    have key : ∀ y : R ⊗[A] integralClosure A K, ∃ b : R,
        (TensorProduct.toIntegralClosure A R K y : R ⊗[A] K) = b ⊗ₜ[A] (1 : K) := by
      intro y
      induction y with
      | tmul b c =>
        obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 c.2
        refine ⟨r • b, ?_⟩
        rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
        rfl
      | add u v hu hv =>
        obtain ⟨a, ha⟩ := hu
        obtain ⟨b, hb⟩ := hv
        exact ⟨a + b, by rw [map_add (f := _), Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
    obtain ⟨b, hb⟩ := key y
    refine ⟨b, ?_⟩
    apply e.injective
    rw [AlgEquiv.commutes, ← hy', hb]
    rfl

end GlobalTheory.GoodEtaleBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
section
open MeasureTheory Matrix

namespace GlobalTheory.DetFactor

variable {k : Type} [Field k] {m : ℕ}

noncomputable def diagGL (n : ℕ) : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (diagonalRingHom (Fin n) k).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem diagGL_val {n : ℕ} (d : Fin n → kˣ) : ((diagGL n d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (d i : k)) := rfl

noncomputable def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) : GL (Fin n) k :=
  nonsingInvUnit M (isUnit_iff_ne_zero.mpr h)

@[simp] theorem toGL_val {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) :
    ((toGL M h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = M := rfl

theorem conj_transvection {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    diagonal (fun l => if l = i then (2 : k) else 1) * transvection i j t
      = transvection i j (2 * t) * diagonal (fun l => if l = i then (2 : k) else 1) := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul, mul_diagonal]
  by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases hbi : b = i <;> by_cases hab : a = b <;>
    simp_all [single, one_apply, eq_comm] <;> ring

theorem det_diag2_ne {n : ℕ} (h2 : (2 : k) ≠ 0) (i : Fin n) :
    (diagonal (fun l => if l = i then (2 : k) else 1)).det ≠ 0 := by
  rw [det_diagonal, Finset.prod_ne_zero_iff]
  intro l _
  split_ifs <;> simp [h2]

theorem det_transvection_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    (transvection i j t).det ≠ 0 := by
  rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero

theorem map_transvection_eq_one (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) {i j : Fin n}
    (hij : i ≠ j) (t : k) : c (toGL (transvection i j t) (det_transvection_ne hij t)) = 1 := by
  set D := toGL _ (det_diag2_ne h2 i)
  have h1 : D * toGL (transvection i j t) (det_transvection_ne hij t)
      = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) * D := by
    apply Units.ext; simp only [Units.val_mul, toGL_val, D]; exact conj_transvection hij t
  have h3 : toGL (transvection i j t) (det_transvection_ne hij t) * toGL (transvection i j t) (det_transvection_ne hij t)
      = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) := by
    apply Units.ext; simp only [Units.val_mul, toGL_val]; rw [transvection_mul_transvection_same (h := hij), two_mul]
  have e1 := congrArg c h1
  have e3 := congrArg c h3
  rw [map_mul, map_mul, mul_comm (c D)] at e1
  have e1' := mul_right_cancel e1
  rw [map_mul, ← e1'] at e3
  exact (mul_eq_left.mp e3)

theorem det_perm_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) : (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) k).det ≠ 0 := by
  have := det_permutation (R := k) σ
  simp only [Equiv.Perm.permMatrix] at this
  rw [this]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem map_diagGL_perm {n : ℕ} (c : GL (Fin n) k →* ℂˣ) (σ : Equiv.Perm (Fin n)) (d : Fin n → kˣ) :
    c (diagGL n (d ∘ σ)) = c (diagGL n d) := by
  set P := toGL _ (det_perm_ne (k := k) σ)
  have h1 : P * diagGL n d = diagGL n (d ∘ σ) * P := by
    apply Units.ext
    simp only [Units.val_mul, toGL_val, P, diagGL_val]
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext a b
    simp [diagonal_apply, Equiv.eq_symm_apply]
  have e := congrArg c h1
  rw [map_mul, map_mul, mul_comm (c P)] at e
  exact (mul_right_cancel e).symm

theorem map_diagGL_eq (c : GL (Fin (m + 1)) k →* ℂˣ) (d : Fin (m + 1) → kˣ) :
    c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0) (∏ i, d i) := by
  have hs : ∀ i (x : kˣ), c (diagGL (m + 1) (Pi.mulSingle i x)) = c (diagGL (m + 1) (Pi.mulSingle 0 x)) := by
    intro i x
    rw [← map_diagGL_perm c (Equiv.swap 0 i) (Pi.mulSingle i x)]
    congr 2
    simp [Pi.mulSingle_comp_equiv]
  have e : c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))) (∏ i, Pi.mulSingle i (d i)) := by
    rw [Finset.univ_prod_mulSingle]; rfl
  rw [e, map_prod, map_prod]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply]
  exact Finset.prod_congr rfl (fun i _ => hs i (d i))

theorem factors_through_det (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) :
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) := by
  cases n with
  | zero =>
    refine ⟨1, fun g => ?_⟩
    have : g = 1 := Units.ext (Matrix.ext fun i _ => i.elim0)
    simp [this]
  | succ m =>
    refine ⟨(c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0), fun g => ?_⟩
    set χ := (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0)
    let P : Matrix (Fin (m + 1)) (Fin (m + 1)) k → Prop := fun M =>
      ∀ u : GL (Fin (m + 1)) k, (u : Matrix _ _ k) = M → c u = χ (Matrix.GeneralLinearGroup.det u)
    have hg : Matrix.det (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    refine diagonal_transvection_induction_of_det_ne_zero P (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) hg ?_ ?_ ?_ g rfl
    · intro D hD u hu
      have hD' : ∀ i, D i ≠ 0 := by
        intro i; rw [det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
      have hu' : u = diagGL (m + 1) (fun i => Units.mk0 (D i) (hD' i)) := by
        apply Units.ext; rw [hu, diagGL_val]; rfl
      have hdet : Matrix.GeneralLinearGroup.det u = ∏ i, Units.mk0 (D i) (hD' i) := by
        apply Units.ext; simp [hu, det_diagonal]
      rw [hdet, hu', map_diagGL_eq]
    · intro t u hu
      have hu' : u = toGL (transvection t.i t.j t.c) (det_transvection_ne t.hij t.c) := Units.ext hu
      have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
        apply Units.ext; simp [hu, TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]
      rw [hdet, map_one, hu']
      exact map_transvection_eq_one h2 c t.hij t.c
    · intro A B hA hB PA PB u hu
      have hu' : u = toGL A hA * toGL B hB := Units.ext (by simp [hu])
      rw [hu', map_mul, map_mul, PA _ rfl, PB _ rfl, ← map_mul]

end GlobalTheory.DetFactor

theorem GlobalTheory.ghom_factors_through_det : ∀ {k : Type} [Field k], (2 : k) ≠ 0 → ∀ {n : ℕ} (c : GL (Fin n) k →* ℂˣ),
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) :=
  by intro k _ h2 n c; exact GlobalTheory.DetFactor.factors_through_det h2 c
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeckeTermDecayIntegrand
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay

noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay

theorem hasDerivAt_qZ : ∀ (σ : ℂ) (a : ℤ) (b m : ℕ) (y : ℝ), y ≠ 0 → ∀ t : ℝ,
    HasDerivAt (qZ σ a b m y) (-(a : ℂ) * qZ σ (a + 1) b m y t
      + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t)) t := by
  intro σ a b m y hy t
  have hu := GlobalTheory.HeckeTwo.TermSmooth.u_ne hy t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp.add_const ((y : ℂ) * I)
  have h2 := (hasDerivAt_zpow (-a) ((t : ℂ) + (y : ℂ) * I) (Or.inl hu)).comp t h1
  have h3 : HasDerivAt (fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))) ((2 * t : ℝ) : ℂ) t := by
    have : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).add_const (y ^ 2))
    exact this.ofReal_comp
  have h4 := (Complex.hasStrictDerivAt_cpow_const (c := -σ - (b : ℂ))
      (Complex.ofReal_mem_slitPlane.2 hQ)).hasDerivAt.comp t h3
  have h := (h2.mul h4).mul_const ((y : ℂ) ^ m)
  refine h.congr_deriv ?_
  simp only [qZ, Function.comp_def]
  rw [show -(a + 1) = -a - 1 by ring, show -(a - 1) = -a + 1 by ring, zpow_add_one₀ hu,
    show -σ - ((b + 1 : ℕ) : ℂ) = -σ - (b : ℂ) - 1 by push_cast; ring]
  push_cast
  ring

end GlobalTheory.HeckeTwo.TermDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictlySemistableChartAtOfSmoothStatement
section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasStrictlySemistableChartAt_of_smooth : ∀ (O : Type) [CommRing O] (ϖ : O) (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (x : X), x ∈ V → Smooth (V.ι ≫ p) → GlobalTheory.SSG.ChartAt ϖ p x := by
  first | (exact @GlobalTheory.SSG.chartAt_of_smooth) | (exact GlobalTheory.SSG.chartAt_of_smooth) | (intros; apply GlobalTheory.SSG.chartAt_of_smooth  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFourierTermWirtingerWordDifferentiableOn
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.TermHol


open Classical in
theorem wirtWord_eq_sum (F : Type) [Field F] [NumberField F] (b ν : F) (hb : b ≠ 0) (hJ : (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane))
    (w : List (Emb F × Bool)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (qf : ι → Emb F → ℕ), ∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F,
      wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z = ∑ i, c i * termQ σ b ν (qf i) z := by
  have hU := GlobalTheory.HeckeTwo.GoodAdd.upperHalf_isOpen F
  induction w with
  | nil =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun σ _ z _ => ?_⟩
    simp [wirtWord_nil, termQ_zero]
  | cons x ws ih =>
    obtain ⟨ι, _, c, qf, h⟩ := ih
    obtain ⟨τ₀, bar⟩ := x
    refine ⟨ι ⊕ ι, inferInstance,
      Sum.elim (fun i => c i * (2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ)) / 2)
        (fun i => (if bar then I else -I) * c i * ((τ₀ b : ℝ) : ℂ) / 2),
      Sum.elim qf (fun i => qf i + Pi.single τ₀ 1), fun σ hσ z hz => ?_⟩
    rw [wirtWord_cons]
    rw [GlobalTheory.HeckeTwo.GoodAdd.wirt_congr hU (g := fun z => ∑ i, c i * termQ σ b ν (qf i) z)
      (fun z hz => h σ hσ z hz) _ _ hz]
    have hd := fun i => _root_.GlobalTheory.HeckeTwo.termQ_fderiv F b ν hb hJ σ hσ (qf i) z hz τ₀
    have hF : HasFDerivAt (fun z => ∑ i, c i * termQ σ b ν (qf i) z)
        (∑ i, c i • fderiv ℝ (termQ σ b ν (qf i)) z) z :=
      HasFDerivAt.fun_sum fun i _ => ((hd i).1.hasFDerivAt.const_mul (c i))
    simp only [wirt, hF.fderiv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, (hd _).2.1, (hd _).2.2, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end GlobalTheory.HeckeTwo.TermHol


open GlobalTheory.HeckeTwo.TermHol in
theorem GlobalTheory.HeckeTwo.fTerm_wirtWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F,
  DifferentiableOn ℂ (fun σ => wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z) halfPlane := by
  intro F _ _ b ν hb w z hz
  have hJ := _root_.GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet _root_.GlobalTheory.HeckeTwo.hTransAB_hasDerivAt _root_.GlobalTheory.HeckeTwo.hTransAB_differentiableOn
  obtain ⟨ι, _, c, qf, h⟩ := wirtWord_eq_sum F b ν hb hJ w
  refine DifferentiableOn.congr ?_ (fun σ hσ => h σ hσ z hz)
  refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.const_mul ?_ _
  unfold termQ
  refine DifferentiableOn.fun_finsetProd fun τ _ => DifferentiableOn.const_mul ?_ _
  have hy : (τ b : ℝ) * (z τ).im ≠ 0 :=
    mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  exact (hJ (τ ν) (qf i τ) _ hy).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapCompStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineCombinationInChart_specMap_comp : ∀ (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S'] (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), GlobalTheory.SecGlue.IsCombIn V u c w a →
    GlobalTheory.SecGlue.IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  first | exact @GlobalTheory.SecGlue.isCombIn_spMap_comp | exact GlobalTheory.SecGlue.isCombIn_spMap_comp | (intros; apply GlobalTheory.SecGlue.isCombIn_spMap_comp <;> assumption)
end

