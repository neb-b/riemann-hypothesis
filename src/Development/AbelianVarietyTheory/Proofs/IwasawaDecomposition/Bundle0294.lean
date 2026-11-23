module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyResidueFieldUnitBallEquiv
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open IsLocalRing

theorem valuation_le_one_iff_of_lt_iff {K F : Type} [Field K] [NumberField K] [NormedField F]
    (v : HeightOneSpectrum (𝓞 K)) (a : K →+* F)
    (h : ∀ x : K, v.valuation K x < 1 ↔ ‖a x‖ < 1) (x : K) :
    v.valuation K x ≤ 1 ↔ ‖a x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h1 := h x⁻¹
  have hv : 0 < v.valuation K x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx)
  have hn : 0 < ‖a x‖ := norm_pos_iff.mpr ((map_ne_zero a).mpr hx)
  rw [map_inv₀, map_inv₀, norm_inv, inv_lt_one₀ hv, inv_lt_one₀ hn] at h1
  rw [← not_lt, ← not_lt, h1]

theorem exists_embedding_inducing_place (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
    (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 K)) (hl : ((l : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ∃ a : K →+* PadicAlgCl l, ∀ x : K, v.valuation K x < 1 ↔ ‖a x‖ < 1 := by
  classical
  let a₀ : K →+* PadicAlgCl l := (IsAlgClosed.lift (R := ℚ) (S := K) (M := PadicAlgCl l)).toRingHom
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding K l a₀
  have hlw : ((l : ℕ) : 𝓞 K) ∈ w₀.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hw₀]
    have hfin : ‖a₀ ((l : ℕ) : K)‖ < 1 := by
      rw [map_natCast]
      have h1 : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by simp
      rw [h1, PadicAlgCl.norm_extends]
      exact Padic.norm_p_lt_one
    convert hfin using 3
    first | exact map_natCast _ _ | simp
  have := v.isPrime
  have := w₀.isPrime
  haveI := Formalism.BasicNotions.Examples₂.PlOver.liesOver_of_mem v.asIdeal hl
  haveI := Formalism.BasicNotions.Examples₂.PlOver.liesOver_of_mem w₀.asIdeal hlw
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(l : ℤ)}) v.asIdeal
    w₀.asIdeal (K ≃ₐ[ℚ] K)
  let a : K →+* PadicAlgCl l := a₀.comp (σ : K →+* K)
  obtain ⟨v', hv'⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding K l a
  have hvv : v' = v := by
    apply HeightOneSpectrum.ext
    ext y
    have h2 : (σ • y) ∈ w₀.asIdeal ↔ y ∈ v.asIdeal := by
      rw [← hσ]; exact Ideal.smul_mem_pointwise_smul_iff
    rw [← h2, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hv',
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hw₀]
    rfl
  subst hvv
  exact ⟨a, hv'⟩

theorem algebraMap_toZMod_eq {l : ℕ} [Fact l.Prime] {R : Type} [Field R] [Algebra (ZMod l) R]
    (f : ℤ_[l] →+* R) (hf : f (l : ℤ_[l]) = 0) (x : ℤ_[l]) :
    algebraMap (ZMod l) R (PadicInt.toZMod x) = f x := by
  first
  | exact @_root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq
  | exact _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq
  | (apply _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq ..)

theorem isAlgebraic_residueField {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [IsLocalRing B]
    [Algebra (ZMod l) (ResidueField B)] (c : ℤ_[l] →+* B)
    (hcl : c (l : ℤ_[l]) ∈ maximalIdeal B)
    (halg : ∀ b : B, ∃ p : ℤ_[l][X], p.IsPrimitive ∧ p.eval₂ c b = 0) :
    Algebra.IsAlgebraic (ZMod l) (ResidueField B) := by
  have hl : (residue B).comp c (l : ℤ_[l]) = 0 := (residue_eq_zero_iff _).mpr hcl
  have hcomp : (algebraMap (ZMod l) (ResidueField B)).comp PadicInt.toZMod = (residue B).comp c :=
    RingHom.ext fun x => algebraMap_toZMod_eq _ hl x
  refine ⟨fun y => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨p, hp, hb⟩ := halg b
  refine ⟨p.map PadicInt.toZMod, fun h => ?_, ?_⟩
  · have hdvd : Polynomial.C (l : ℤ_[l]) ∣ p := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have h1 : PadicInt.toZMod (p.coeff i) = 0 := by
        have := congrArg (fun q => q.coeff i) h
        simpa using this
      have h2 : p.coeff i ∈ RingHom.ker (PadicInt.toZMod (p := l)) := h1
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at h2
      exact Ideal.mem_span_singleton.mp h2
    have hu := hp _ hdvd
    exact PadicInt.prime_p.not_unit hu
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hb, map_zero]

theorem exists_isPrimitive_eval₂_eq_zero {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) :
    ∃ p : ℤ_[l][X], p.IsPrimitive ∧
      p.eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom) x = 0 := by
  classical
  have hmap : algebraMap ℤ_[l] (PadicAlgCl l) =
      (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom :=
    IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)
  haveI : FaithfulSMul ℤ_[l] (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [hmap]
      exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp fun a b h => Subtype.ext h)
  letI : NormalizedGCDMonoid ℤ_[l] := Classical.arbitrary _
  have hx : IsAlgebraic ℤ_[l] x :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (PadicAlgCl l)).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨p, hp0, hp⟩ := hx
  refine ⟨p.primPart, p.isPrimitive_primPart, ?_⟩
  rw [← hmap]
  exact Polynomial.aeval_primPart_eq_zero hp0 hp

def unitBall {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) : ValuationSubring ℂ :=
  (PadicAlgCl.valued l).v.valuationSubring.comap (ι.symm : ℂ →+* PadicAlgCl l)

theorem mem_unitBall_iff {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (z : ℂ) :
    z ∈ unitBall ι ↔ ‖ι.symm z‖ ≤ 1 := by
  rw [unitBall, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
    ← NNReal.coe_le_coe]
  rfl

theorem nonempty_residueField_unitBall_equiv {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) :
    Nonempty (ResidueField (unitBall ι) ≃+* Formalism.CyclotomicNorms.Fbar l) := by
  classical
  set B := unitBall ι with hB
  let inc : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom
  have hinc : ∀ x : ℤ_[l], ‖inc x‖ = ‖x‖ := fun x => by
    change ‖((x : ℚ_[l]) : PadicAlgCl l)‖ = ‖x‖
    rw [PadicAlgCl.norm_extends]; rfl
  let c : ℤ_[l] →+* B := (ι.toRingHom.comp inc).codRestrict B.toSubring fun x => by
    change ι (inc x) ∈ B
    rw [hB, mem_unitBall_iff, RingEquiv.symm_apply_apply, hinc]
    exact PadicInt.norm_le_one x
  have hcl : c (l : ℤ_[l]) ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨⟨y, hy⟩, hxy⟩ := hu.exists_right_inv
    have h1 : ι (inc (l : ℤ_[l])) * y = 1 := congrArg Subtype.val hxy
    have h2 : inc (l : ℤ_[l]) * ι.symm y = 1 := by
      apply ι.injective
      rw [map_mul, RingEquiv.apply_symm_apply, h1, map_one]
    have h3 := congrArg norm h2
    have h4 : ‖ι.symm y‖ ≤ 1 := (mem_unitBall_iff ι y).mp hy
    rw [norm_mul, hinc, norm_one] at h3
    have h5 : ‖(l : ℤ_[l])‖ < 1 := by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
    nlinarith [norm_nonneg (ι.symm y), norm_nonneg (l : ℤ_[l])]
  have halg : ∀ b : B, ∃ p : ℤ_[l][X], p.IsPrimitive ∧ p.eval₂ c b = 0 := by
    intro b
    obtain ⟨p, hp, h0⟩ := exists_isPrimitive_eval₂_eq_zero (ι.symm (b : ℂ))
    refine ⟨p, hp, Subtype.ext ?_⟩
    have h1 := Polynomial.hom_eval₂ p c B.subtype b
    have h2 := Polynomial.hom_eval₂ p inc ι.toRingHom (ι.symm (b : ℂ))
    have h3 : B.subtype.comp c = ι.toRingHom.comp inc := RingHom.ext fun _ => rfl
    have h4 : ι.toRingHom (ι.symm (b : ℂ)) = B.subtype b := ι.apply_symm_apply _
    rw [h3, ← h4, ← h2] at h1
    have h5 : p.eval₂ inc (ι.symm (b : ℂ)) = 0 := h0
    rw [h5, map_zero] at h1
    exact h1
  have hlR : ((l : ℕ) : ResidueField B) = 0 := by
    have := (residue_eq_zero_iff _).mpr hcl
    simpa using this
  haveI : CharP (ResidueField B) l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hlR
  letI : Algebra (ZMod l) (ResidueField B) := ZMod.algebra _ l
  haveI : Algebra.IsAlgebraic (ZMod l) (ResidueField B) := isAlgebraic_residueField c hcl halg
  haveI : IsAlgClosed (ResidueField B) :=
    GlobalTheory.isAlgClosed_residueField_of_valuationRing_of_isAlgClosed B ℂ
  haveI : IsAlgClosure (ZMod l) (ResidueField B) := ⟨inferInstance, inferInstance⟩
  exact ⟨(IsAlgClosure.equiv (ZMod l) (ResidueField B) (AlgebraicClosure (ZMod l))).toRingEquiv⟩

theorem val_nonneg_iff (D : D7) (lam : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val lam x ↔ (D.plEq lam).valuation D.what₂.LL x ≤ 1 := by
  haveI := D.nfLL
  by_cases hx : x = 0
  · simp [hx]
  rw [D.val_eq lam x hx]
  have h0 : (D.plEq lam).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have h1 := WithZero.log_le_log (x := (D.plEq lam).valuation D.what₂.LL x) (y := 1) h0 one_ne_zero
  rw [WithZero.log_one] at h1
  rw [← h1]
  unfold vAdd
  norm_cast
  omega

theorem nonempty_plSide : ∀ D : D7, Nonempty (PlSide D) := by
  intro D
  haveI := D.nfLL
  haveI := D.galLL
  have key : ∀ lam : D.what₂.places.Pl, ∃ ι : Qbar (D.what₂.places.resChar lam) ≃+* ℂ,
      ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val lam x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1 := by
    intro lam
    obtain ⟨a, ha⟩ := exists_embedding_inducing_place D.what₂.LL (D.what₂.places.resChar lam)
      (D.plEq lam) (Formalism.BasicNotions.Examples₂.PlOver.resChar_mem D lam)
    obtain ⟨ι, hι⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq
      (D.what₂.places.resChar lam) D.what₂.LL a D.what₂.embLL
    refine ⟨ι, fun x => ?_⟩
    have h1 : ι.symm (D.what₂.embLL x) = a x := by
      rw [← hι]; exact ι.symm_apply_apply _
    rw [h1, val_nonneg_iff, valuation_le_one_iff_of_lt_iff _ a ha]
  choose ι hι using key
  exact ⟨⟨ι, hι, fun lam => unitBall (ι lam), fun lam z => mem_unitBall_iff (ι lam) z,
    fun lam => Classical.choice (nonempty_residueField_unitBall_equiv (ι lam))⟩⟩

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieExteriorSquare
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.PolyRep

theorem snd_wedge2_dual {M : ℕ} {R : Type} [CommRing R] (L : Matrix (Fin M) (Fin M) R) (p q : Fin (pairCard M)) :
    TrivSqZeroExt.snd (ChernSpan.wedge2 (Matrix.of fun a b =>
        (TrivSqZeroExt.inl ((1 : Matrix (Fin M) (Fin M) R) a b) + TrivSqZeroExt.inr (L a b) : DualNumber R)) p q)
      = wedge2Lie L p q := by
  simp only [ChernSpan.wedge2, wedge2Lie, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    wedgeRaw, wedgeLieRaw, Matrix.of_apply]
  simp only [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
    smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add]
  ring

theorem lie_wedge2 {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) :
    ρ.wedge2.lie A = wedge2Lie (ρ.lie A) := by
  ext p q
  have h := ev_dual_model ρ.wedge2 A p q
  have e : ∀ D : Mat m (DualNumber R), ρ.wedge2.ev D = ChernSpan.wedge2 (ρ.ev D) :=
    fun D => evEnt_wedge2 ρ.ent D
  have e2 : ρ.ev (R := DualNumber R) (fun τ => Matrix.of fun a b =>
        TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b))
      = Matrix.of fun a b => (TrivSqZeroExt.inl ((1 : Matrix (Fin ρ.M) (Fin ρ.M) R) a b)
        + TrivSqZeroExt.inr (ρ.lie A a b) : DualNumber R) := by
    ext a b : 1
    exact ev_dual_model ρ A a b
  rw [e, e2] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h2
  exact h2.symm.trans (snd_wedge2_dual (ρ.lie A) p q)

end GlobalTheory.GoodMetric.PolyRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieTensorProduct
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PolyRep

theorem lie_tensor {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R]
    (A : Mat m R) :
    (ρ.tensor σ).lie A = kron (ρ.lie A) 1 + kron 1 (σ.lie A) := by
  ext i j
  obtain ⟨⟨a, c⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨b, d⟩, rfl⟩ := finProdFinEquiv.surjective j
  set X : Mat m (DualNumber R) := fun τ => Matrix.of fun a b =>
    TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b) with hX
  have h := ev_dual_model (ρ.tensor σ) A (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d))
  have hk : (ρ.tensor σ).ev X = kron (ρ.ev X) (σ.ev X) := evEnt_kron ρ.ent σ.ent X
  rw [hk] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h2
  have hr : (kron (ρ.lie A) (1 : Matrix (Fin σ.M) (Fin σ.M) R) + kron (1 : Matrix (Fin ρ.M) (Fin ρ.M) R) (σ.lie A))
      (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d))
      = ρ.lie A a b * (1 : Matrix (Fin σ.M) (Fin σ.M) R) c d + (1 : Matrix (Fin ρ.M) (Fin ρ.M) R) a b * σ.lie A c d := by
    simp [kron]
  have hl : kron (ρ.ev X) (σ.ev X) (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d)) = ρ.ev X a b * σ.ev X c d := by
    simp [kron]
  rw [hl, ev_dual_model ρ A a b, ev_dual_model σ A c d] at h2
  rw [← h2]
  refine Eq.trans ?_ hr.symm
  simp [TrivSqZeroExt.snd_mul]
  ring

end GlobalTheory.GoodMetric.PolyRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemSpanAdelicRationalForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem mem_of_avg {K : Type} [Field K] (σ : K →+* ℂ) {V : Type} [AddCommGroup V] [Module K V] {G : Type} [Group G]
    (r : Representation K G V) (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) {M : Type} [AddCommGroup M] [Module ℂ M]
    (j : V →ₛₗ[σ] M) (T : P → M →ₗ[ℂ] M) (hT : ∀ p v, T p (j v) = j (r p v))
    (S : Submodule ℂ M) (hS : ∀ v, (∀ h : P, r h v = ((ψ h : Kˣ) : K) • v) → j v ∈ S)
    (Fn : M) (hF : Fn ∈ Submodule.span ℂ (Set.range j)) (hFn : ∀ p, T p Fn = σ ((ψ p : Kˣ) : K) • Fn) : Fn ∈ S := by
  let Pj : M →ₗ[ℂ] M := (Nat.card P : ℂ)⁻¹ • ∑ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p
  have hPj : ∀ x, Pj x = (Nat.card P : ℂ)⁻¹ • ∑ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p x := by
    intro x
    simp only [Pj, LinearMap.smul_apply, LinearMap.sum_apply]
  have hcard : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hfix : Pj Fn = Fn := by
    have hterm : ∀ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p Fn = Fn := by
      intro p
      rw [hFn, smul_smul, ← map_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, map_one, one_smul]
    rw [hPj, Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hmap : ∀ v, Pj (j v) ∈ S := by
    intro v
    have e : Pj (j v) = j ((Nat.card P : K)⁻¹ • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hPj, map_smulₛₗ, map_sum, map_inv₀, map_natCast]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smulₛₗ, hT]
    rw [e]
    exact hS _ (avg_level K V G r P ψ v)
  have hle : Submodule.span ℂ (Set.range j) ≤ S.comap Pj :=
    Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact hmap v)
  have hPF : Pj Fn ∈ S := hle hF
  rwa [hfix] at hPF

theorem exists_rowForm (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G)
    (ψ : P →* D.what₂.LLˣ) (t : T) (f : A.fam.amb.FR t) (hlv : ∀ h : P, (A.fam.R t).r h f = ((ψ h : D.what₂.LLˣ) : D.what₂.LL) • f) :
    ∃ x, rowForm A P ψ t x = f :=
  (GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char _ _ _ (A.fam.R t).r P ψ f).2 hlv

theorem jR_mem_span (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (g : A.fam.amb.FR t)
    (hg : ∀ h : (F.lvl b).P, (A.fam.R t).r h g = (((F.lvl b).ψ h : D.what₂.LLˣ) : D.what₂.LL) • g)
    (Y : Bridge.Gf D.sp.X' → R.cX.W) (hY : Y = R.B.jR t g) :
    Y ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  obtain ⟨x, hx⟩ := exists_rowForm D G Pl0 T A (F.lvl b).P (F.lvl b).ψ t g hg
  subst hY
  subst hx
  exact Submodule.subset_span ⟨x, rfl⟩


set_option maxHeartbeats 2000000 in
theorem proj_span : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → Fn ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F b t Fn hF hQ
  have hB := Bridge.ClassPres.extBij_holds (R.B.R t).pres
  have hF0 : Fn ∈ Submodule.span ℂ (Set.range (R.B.R t).pres.extL) := by rw [hB.2]; exact hF
  have hF' : Fn ∈ Submodule.span ℂ (Set.range (R.B.jR t)) := hF0
  obtain ⟨κ, hκ⟩ : ∃ κ : (F.lvl b).P → (levEnv D.sp.X' R.βX (R.datXt t)).Q,
      ∀ p, (R.B.R t).act_tie.red (κ p) = (p : G) :=
    ⟨fun p => ((R.B.R t).act_tie.red_surj (p : G)).choose,
      fun p => ((R.B.R t).act_tie.red_surj (p : G)).choose_spec⟩
  obtain ⟨gl, gl_apply⟩ : ∃ gl : (F.lvl b).P → (Bridge.Gf D.sp.X' → R.cX.W) →ₗ[ℂ] (Bridge.Gf D.sp.X' → R.cX.W),
      ∀ p H, gl p H = Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) H :=
    ⟨fun p => { toFun := fun H => Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) H
                map_add' := by intro H H'; funext h; simp only [Bridge.g0Act, Pi.add_apply, smul_add]
                map_smul' := by intro c H; funext h; simp only [Bridge.g0Act, Pi.smul_apply, RingHom.id_apply]; rw [smul_comm] },
      fun _ _ => rfl⟩
  have hact : ∀ (p : (F.lvl b).P) (f : A.fam.amb.FR t), gl p (R.B.jR t f) = R.B.jR t ((A.fam.R t).r p f) := by
    intro p f
    have e : (R.B.R t).pres.extL (A.leftGroupActionRight t (p : G) f) =
        Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) ((R.B.R t).pres.extL f) :=
      (R.B.R t).act_tie.act_eq (p : G) (κ p) (hκ p) f
    exact (gl_apply p _).trans e.symm
  have hg : ∀ p : (F.lvl b).P, gl p Fn = D.what₂.embLL (((F.lvl b).ψ p : D.what₂.LLˣ) : D.what₂.LL) • Fn := by
    intro p
    have hq : (R.B.R t).act_tie.red (κ p) ∈ (F.lvl b).P := by rw [hκ p]; exact p.2
    rw [gl_apply]
    funext h
    simp only [Bridge.g0Act, Pi.smul_apply]
    rw [hQ (κ p) hq h]
    have hp : (⟨_, hq⟩ : (F.lvl b).P) = p := Subtype.ext (hκ p)
    rw [hp, smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
  exact mem_of_avg D.what₂.embLL (A.fam.R t).r (F.lvl b).P (F.lvl b).ψ (R.B.jR t) gl hact _
    (fun v hv => jR_mem_span D G Pl0 T A Ks R F b t v hv _ rfl) Fn hF' hg

end GlobalTheory.TopSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadUpdSKeep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem read_updS_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (err : type_of% R.err0)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ∃ (Y' : Read (A3 := A3) ((R.updS R.kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS R.kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  refine ⟨reFaceRead (R.updS R.kap lam) F Dc Sp Zsc err X0 Y,
    reFaceReadL (R.updS R.kap lam) F Dc Sp Zsc err X0 Y (scalReadL R F lam hX X0 Y Z),
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (HEq.refl Y.jA :))
  · exact (by with_unfolding_all exact (HEq.refl Y.jA0 :))
  · exact (by with_unfolding_all exact (HEq.refl Y.eMt :))
  · exact (by with_unfolding_all exact (HEq.refl Y.PY :))
  · exact (by with_unfolding_all exact (HEq.refl Y.eFT :))
  · exact (by with_unfolding_all exact (HEq.refl Y.IL :))
  · exact (by with_unfolding_all exact (HEq.refl Y.PW :))
  · exact (by with_unfolding_all exact (HEq.refl Y.eE :))
  · exact (by with_unfolding_all exact (HEq.refl Y.mj.eW :))
  · exact (by with_unfolding_all exact (HEq.refl Z.eRR :))
  · exact (by with_unfolding_all exact (HEq.refl Z.jW :))

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfIsNef
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory

theorem IsAmpleLB.tens_of_isNef : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, GlobalTheory.IsAmpleLB A → (letI := GlobalTheory.algebraΓOfHom f; GlobalTheory.IsNef k N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens A N) := by
  intro h k _ X f hf A N hA hN
  letI := GlobalTheory.algebraΓOfHom f
  refine IsAmpleLB.tens_of_forall_isPsEff k X f hf A N hA hN.isLB fun Z hZ => ?_
  haveI := isIntegral_red hZ
  letI := algebraΓAlong k (redι Z)
  have hi := appTop_algebraMap_along k (redι Z)
  have hp : IsProjOver (strHom k (X := X)) := by rwa [strHom_eq (f := f) fun _ => rfl]
  have hp' : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    obtain ⟨n, e, he, hs⟩ := hp
    exact ⟨n, redι Z ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩
  exact IsNef.isPsEff h k _ hp' _ (hN.pull_of_isClosedImmersion (redι Z) hi)

end GlobalTheory
end
end

