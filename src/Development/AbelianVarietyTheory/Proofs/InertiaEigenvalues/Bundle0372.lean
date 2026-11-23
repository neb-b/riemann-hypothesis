module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfLinearIndependentDdRE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByCyclotomicKernelEtalePhiSolutionMemWach
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittApproxFrobeniusPerfection
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteBreuilKisinQuotientPrimePowXPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKFin

theorem finite_witt_quot (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [Finite F] [CharP F l] (n : ℕ) :
    Finite (WittVector l F ⧸ Ideal.span {(l : WittVector l F) ^ n}) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hker : RingHom.ker (WittVector.truncate (p := l) (R := F) n) =
      Ideal.span {(l : WittVector l F) ^ n} := by
    ext x
    rw [WittVector.mem_ker_truncate, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
  exact Finite.of_equiv _ ((Ideal.quotEquivOfEq hker).symm.trans
    (RingHom.quotientKerEquivOfSurjective (WittVector.truncate_surjective l n F))).toEquiv.symm

theorem finite_quot : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n c : ℕ),
    Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c})) := by
  intro l _ K bk n c
  haveI : Finite (Wq l bk.a ⧸ Ideal.span {(l : Wq l bk.a) ^ n}) := finite_witt_quot l (Fq l bk.a) n
  let J : Ideal (Wq l bk.a) := Ideal.span {(l : Wq l bk.a) ^ n}
  let I : Ideal bk.S := Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c}
  let g : (Fin c → Wq l bk.a ⧸ J) → bk.S ⧸ I := fun t => Ideal.Quotient.mk I
    (∑ i ∈ Finset.range c, C (if h : i < c then (t ⟨i, h⟩).out else 0) * X ^ i)
  refine Finite.of_surjective g ?_
  intro q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨fun i => Ideal.Quotient.mk J (coeff (i : ℕ) s), ?_⟩
  let w : ℕ → Wq l bk.a := fun i => if h : i < c then (Ideal.Quotient.mk J (coeff i s)).out else 0
  show Ideal.Quotient.mk I (∑ i ∈ Finset.range c, C (w i) * X ^ i) = Ideal.Quotient.mk I s
  rw [Ideal.Quotient.eq]
  have hw : ∀ i < c, w i - coeff i s ∈ J := by
    intro i hi
    simp only [w, dif_pos hi]
    rw [← Ideal.Quotient.eq]
    exact Ideal.Quotient.mk_out _
  have hsplit : (∑ i ∈ Finset.range c, C (w i) * X ^ i) - s =
      (∑ i ∈ Finset.range c, C (w i - coeff i s) * X ^ i) +
        ((∑ i ∈ Finset.range c, C (coeff i s) * X ^ i) - s) := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (hw i (Finset.mem_range.1 hi))
    rw [← hy, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [PowerSeries.coeff_C_mul_X_pow, Finset.sum_ite_eq', hm]

end GlobalTheory.BKFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.ZSumOne

open CategoryTheory

variable {G : Type} [Group G] [Fintype G]

theorem zOf_coeff (χ : G → ℂ) (y : G) : (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.single_apply,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem irr_one_eq_finrank {χ : G → ℂ} {V : FDRep ℂ G} (hV : ∀ x, V.character x = χ x) :
    χ 1 = (Module.finrank ℂ V : ℂ) := by
  rw [← hV 1, FDRep.char_one]

theorem zOf_eq_zIdem (χ : G → ℂ) (V : FDRep ℂ G) (hV : ∀ x, V.character x = χ x) :
    zOf χ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem V := by
  have h1 := irr_one_eq_finrank hV
  unfold zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h1, ← hV x⁻¹]
  rfl

theorem zOf_injOn : Set.InjOn (zOf (G := G)) {χ | IsIrr χ} := by
  intro χ hχ χ' hχ' h
  obtain ⟨V, hs, hV⟩ := hχ
  obtain ⟨V', hs', hV'⟩ := hχ'
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 := irr_one_eq_finrank hV
  have h1' := irr_one_eq_finrank hV'
  have e1 := congrArg (fun a => a.coeff 1) h
  simp only [zOf_coeff, inv_one] at e1
  rw [h1, h1'] at e1
  have e2 : ((Module.finrank ℂ V * Module.finrank ℂ V : ℕ) : ℂ) =
      ((Module.finrank ℂ V' * Module.finrank ℂ V' : ℕ) : ℂ) := by
    push_cast
    field_simp at e1
    linear_combination e1
  have hn : Module.finrank ℂ V = Module.finrank ℂ V' := Nat.mul_self_inj.mp (by exact_mod_cast e2)
  have h11 : χ 1 = χ' 1 := by rw [h1, h1', hn]
  haveI := PI.GreenLabelSurjWork.nontrivial_of_simple V hs
  have hpos : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hk : χ 1 / (Fintype.card G : ℂ) ≠ 0 := div_ne_zero (h1 ▸ hpos) hc
  funext y
  have e3 := congrArg (fun a => a.coeff y⁻¹) h
  simp only [zOf_coeff, inv_inv] at e3
  rw [← h11] at e3
  exact mul_left_cancel₀ hk e3

theorem zOf_image :
    zOf '' {χ : G → ℂ | IsIrr χ} =
      {z : MonoidAlgebra ℂ G | ∃ τ : FDRep ℂ G, Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z} := by
  ext z
  constructor
  · rintro ⟨χ, ⟨V, hs, hV⟩, rfl⟩
    exact ⟨V, hs, (zOf_eq_zIdem χ V hV).symm⟩
  · rintro ⟨τ, hs, rfl⟩
    exact ⟨τ.character, ⟨τ, hs, fun _ => rfl⟩, zOf_eq_zIdem _ τ fun _ => rfl⟩

end GlobalTheory.GLq.ZSumOne

namespace GlobalTheory.GLq

theorem irr_finite_and_finsum_zOf_eq_one : ∀ (G : Type) [Group G] [Fintype G],
    {χ : G → ℂ | IsIrr χ}.Finite ∧ ∑ᶠ χ ∈ {χ : G → ℂ | IsIrr χ}, zOf χ = 1 := by
  intro G _ _
  have hZ := GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one G
  rw [← ZSumOne.zOf_image] at hZ
  refine ⟨Set.Finite.of_finite_image hZ.1 ZSumOne.zOf_injOn, ?_⟩
  have himg := finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) (ZSumOne.zOf_injOn (G := G))
  rw [← himg]
  exact hZ.2

end GlobalTheory.GLq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteProjectiveModuleElementDescentEqualizer
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.ProjDescent

section SlopeTestRemainingChoices

variable {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N}

theorem span_top (h : SemiBC u) : Submodule.span B (Set.range u) = ⊤ := by
  obtain ⟨w, -, hw⟩ := h (N ⧸ Submodule.span B (Set.range u)) 0
  have h1 := hw (Submodule.mkQ _) fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨x, rfl⟩)
  have h2 := hw 0 fun _ => rfl
  rw [← Submodule.ker_mkQ (Submodule.span B (Set.range u)), h1, ← h2, LinearMap.ker_zero]

theorem induction (h : SemiBC u) (P : N → Prop) (h0 : ∀ x, P (u x)) (h1 : ∀ y z, P y → P z → P (y + z))
    (h2 : ∀ (b : B) y, P y → P (b • y)) (y : N) : P y := by
  have hy : y ∈ Submodule.span B (Set.range u) := by rw [span_top h]; trivial
  induction hy using Submodule.span_induction with
  | mem _ hx => obtain ⟨x, rfl⟩ := hx; exact h0 x
  | zero => rw [← map_zero u]; exact h0 0
  | add y z _ _ hy hz => exact h1 y z hy hz
  | smul b y _ hy => exact h2 b y hy

end SlopeTestRemainingChoices

theorem descent : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), p.comp f = q.comp f → Function.Injective f → (∀ b, p b = q b → b ∈ f.range) → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P] (PB : Type) [AddCommGroup PB] [Module B PB] (PD : Type) [AddCommGroup PD] [Module D PD] (u : P →ₛₗ[f] PB) (u₁ : PB →ₛₗ[p] PD) (u₂ : PB →ₛₗ[q] PD) (w : P →ₛₗ[p.comp f] PD), SemiBC u → SemiBC w → (∀ x, w x = u₁ (u x)) → (∀ x, w x = u₂ (u x)) → Function.Injective u ∧ ∀ z, u₁ z = u₂ z → ∃ y, u y = z := by
  intro A B D _ _ _ f p q hpq hf hfix P _ _ _ _ PB _ _ PD _ _ u u₁ u₂ w hu hw h₁ h₂
  classical
  obtain ⟨n, s, g, -, -, hsg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  have hx : ∀ x, s (g x) = x := fun x => LinearMap.congr_fun hsg x
  set e : Fin n → P := fun i => s (fun j => if i = j then 1 else 0) with he
  have hdec : ∀ c : Fin n → A, u (s c) = ∑ i, f (c i) • u (e i) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.pi_apply_eq_sum_univ s c, map_sum]
    simp only [LinearMap.map_smulₛₗ, e]
  obtain ⟨WB, hWB, -⟩ := hu (Fin n → B)
    { toFun := fun x i => f (g x i)
      map_add' := fun x y => funext fun i => by simp
      map_smul' := fun a x => funext fun i => by simp }
  obtain ⟨WD, hWD, -⟩ := hw (Fin n → D)
    { toFun := fun x i => p (f (g x i))
      map_add' := fun x y => funext fun i => by simp
      map_smul' := fun a x => funext fun i => by simp }
  have hWB' : ∀ x i, WB (u x) i = f (g x i) := fun x i => congrFun (hWB x) i
  have hWD' : ∀ x i, WD (w x) i = p (f (g x i)) := fun x i => congrFun (hWD x) i
  have hrec : ∀ z, z = ∑ i, WB z i • u (e i) := by
    intro z
    refine induction hu (fun z => z = ∑ i, WB z i • u (e i)) (fun x => ?_) (fun y z hy hz => ?_)
      (fun b y hy => ?_) z
    · conv_lhs => rw [← hx x]
      rw [hdec]; simp only [hWB']
    · conv_lhs => rw [hy, hz]
      simp only [map_add (f := _), Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · conv_lhs => rw [hy]
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hp : ∀ z i, p (WB z i) = WD (u₁ z) i := by
    intro z
    refine induction hu (fun z => ∀ i, p (WB z i) = WD (u₁ z) i) (fun x i => ?_)
      (fun y z hy hz i => ?_) (fun b y hy i => ?_) z
    · rw [← h₁, hWD', hWB']
    · simp only [map_add (f := _), Pi.add_apply, hy, hz]
    · simp only [map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, hy]
  have hq : ∀ z i, q (WB z i) = WD (u₂ z) i := by
    intro z
    refine induction hu (fun z => ∀ i, q (WB z i) = WD (u₂ z) i) (fun x i => ?_)
      (fun y z hy hz i => ?_) (fun b y hy i => ?_) z
    · rw [← h₂, hWD', hWB']
      exact (RingHom.congr_fun hpq (g x i)).symm
    · simp only [map_add (f := _), Pi.add_apply, hy, hz]
    · simp only [map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, hy]
  refine ⟨fun x y hxy => ?_, fun z hz => ?_⟩
  · have hg : g x = g y := funext fun i => hf (by rw [← hWB', ← hWB', hxy])
    rw [← hx x, ← hx y, hg]
  · have hb : ∀ i, ∃ b, f b = WB z i := fun i => RingHom.mem_range.1 (hfix _ (by rw [hp, hq, hz]))
    choose b hb using hb
    exact ⟨s b, by rw [hdec]; simp only [hb]; exact (hrec z).symm⟩

end GlobalTheory.BSP.ProjDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.LetterDim

theorem card_le_of_idem {R : Type} [CommRing R] {e : R} (he : e * e = e) (he0 : e ≠ 0)
    {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → κ → R)
    (h : ∀ r : ι → R, (∀ j, ∑ i, r i * a i j = 0) → ∀ i, e * r i = 0) :
    Fintype.card ι ≤ Fintype.card κ := by
  let I : Ideal R := Ideal.span {1 - e}
  have hI : ∀ x, x ∈ I ↔ e * x = 0 := by
    intro x
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, rfl⟩
      linear_combination (-c) * he
    · intro hx
      exact ⟨x, by linear_combination -hx⟩
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by
    intro hT
    have : (1 : R) ∈ I := by rw [hT]; trivial
    rw [hI, mul_one] at this
    exact he0 this)
  have hli : LinearIndependent (R ⧸ I) (fun i j => Ideal.Quotient.mk I (a i j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose r hr using fun i => Ideal.Quotient.mk_surjective (g i)
    rw [← hr, Ideal.Quotient.eq_zero_iff_mem, hI, ← he, mul_assoc]
    refine h (fun i => e * r i) (fun j => ?_) i
    have := congrFun hg j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← hr, ← map_mul,
      ← map_sum] at this
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  simpa using hli.fintype_card_le_finrank

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V]


open GlobalTheory.DRFil in
theorem component_le [FiniteDimensional Qp K] [CharZero Qp] (hF : IsField F) (ρ : Representation LL G V)
    (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    finrank LL ↥(DdRE PD ρ τ) ≤ finrank LL V := by
  haveI := nontrivial_dR PD
  let b := Module.finBasis LL ↥(DdRE PD ρ τ)
  let v := Module.finBasis LL V
  have hli : LinearIndependent LL (fun i => (b i : V ⊗[Qp] F)) :=
    b.linearIndependent.map' (DdRE PD ρ τ).subtype (Submodule.ker_subtype _)
  have h := indep_of_linearIndependent_DdRE PD ρ τ _ hF (fun i => (b i).2) hli
  have := card_le_of_idem (idem_mul_idem (F := F) τ) (idem_ne_zero (F := F) τ)
    (fun i j => ext Qp F (v.coord j) (b i : V ⊗[Qp] F)) (fun r hr => h r (by
      rw [eq_sum_basis v (∑ i, sm Qp F LL V (r i) (b i : V ⊗[Qp] F))]
      refine Finset.sum_eq_zero fun j _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [ext_sm, sm_self]
      rw [hr j, map_zero, LinearMap.zero_apply]))
  simpa using this

theorem component_eq [CharZero Qp] (hF : IsField F) (ρ : Representation LL G V)
    (hc : Nat.card (K →ₐ[Qp] LL) = finrank Qp K) (h : IsDR PD ρ) (τ : K →ₐ[Qp] LL) :
    finrank LL ↥(DdRE PD ρ τ) = finrank LL V := by
  haveI := PD.finK
  haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le PD hF ρ).1
  haveI : ∀ τ, FiniteDimensional LL ↥(DdRE PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  rw [Nat.card_eq_fintype_card] at hc
  have hs := (GlobalTheory.DeRhamSplit.finrank_DdR PD ρ hc 0).1
  unfold IsDR at h
  refine (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (g := fun _ => finrank LL V)
    fun τ _ => component_le PD hF ρ τ).1 ?_ τ (Finset.mem_univ τ)
  rw [← hs, h, Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]


omit [FiniteDimensional Qp LL] in
theorem finite_Dcris (ρ : Representation LL G V) (h : IsCrys PD ρ) : Module.Finite LL ↥(Dcris PD ρ) := by
  haveI := PD.finK₀
  rcases Nat.eq_zero_or_pos (finrank LL V) with h0 | h0
  · haveI : Subsingleton V := finrank_zero_iff.1 h0
    infer_instance
  · exact FiniteDimensional.of_finrank_pos (by
      unfold IsCrys at h
      rw [h]
      exact Nat.mul_pos finrank_pos h0)


omit [FiniteDimensional Qp LL] in
open GlobalTheory.RegularRing in
theorem letter_eq [IsDomain B] (ρ : Representation LL G V)
    (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (h : IsCrys PD ρ) (τ : K₀ →ₐ[Qp] LL) :
    finrank LL ↥(DcrisL PD ρ τ) = finrank LL V := by
  haveI := PD.finK₀
  haveI := finite_Dcris PD ρ h
  have hle : ∀ (n : ℕ) (τ τ' : K₀ →ₐ[Qp] LL), (∀ c, τ' c = τ (PD.σ^[n] c)) →
      finrank LL ↥(DcrisL PD ρ τ') ≤ finrank LL ↥(DcrisL PD ρ τ) := by
    intro n
    induction n with
    | zero =>
      intro τ τ' h
      rw [show τ' = τ from AlgHom.ext h]
    | succ n ih =>
      intro τ τ' h
      exact (ih (τ.comp PD.σ) τ' fun c => by rw [h, Function.iterate_succ_apply']; rfl).trans
        (letter_le PD (LL := LL) ρ τ _ fun _ => rfl)
  have heq : ∀ τ', finrank LL ↥(DcrisL PD ρ τ') = finrank LL ↥(DcrisL PD ρ τ) := fun τ' => by
    obtain ⟨n, hn⟩ := exists_pow_sigma PD LL hc τ τ'
    obtain ⟨n', hn'⟩ := exists_pow_sigma PD LL hc τ' τ
    exact le_antisymm (hle n _ _ hn) (hle n' _ _ hn')
  rw [Nat.card_eq_fintype_card] at hc
  have hs : finrank LL ↥(Dcris PD ρ) = ∑ τ', finrank LL ↥(DcrisL PD ρ τ') :=
    GlobalTheory.DeRhamSplit.finrank_eq_sum hc (GlobalTheory.DeRhamSplit.mulHom Qp K₀ B LL V) (Dcris PD ρ)
      fun a x hx => (GlobalTheory.FontCmp.mK PD ρ a ⟨x, hx⟩).2
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, hc] at hs
  unfold IsCrys at h
  exact Nat.eq_of_mul_eq_mul_left finrank_pos (hs.symm.trans h)

end General

theorem tied_letter_component_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) → IsCrys (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) ∧ (Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → IsDR (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  exact ⟨letter_eq (P.PD K) ρ, component_eq (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ⟩

end GlobalTheory.Per.LetterDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByCyclotomicKernelEtalePhiSolutionMemWachStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedByCyclotomicKernel_etalePhi_solution_mem_wach :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ)
      (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R),
      IoW I → ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) R.EE) (A' : Matrix (Fin q) (Fin q) R.EE)
      (Y : Matrix (Fin p) (Fin q) R.EE) (U : Matrix (Fin p) (Fin q) (RW LL)),
      IsUnit A → IsUnit A' → (∀ i j, FixH AI K (U i j)) →
      HMul.hMul (α := Matrix (Fin p) (Fin p) (RW LL)) (β := Matrix (Fin p) (Fin q) (RW LL))
        (A.map I.ioE) (U.map (φRW LL)) =
        HMul.hMul (α := Matrix (Fin p) (Fin q) (RW LL)) (β := Matrix (Fin q) (Fin q) (RW LL))
          U (A'.map I.ioE) + Y.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE := by
  intro l _ P AI K s LL hG Γ R I hW p q A A' Y U _ hA' hU h i j
  obtain ⟨C, hC⟩ := hA'.exists_right_inv
  let σ := (finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm
  obtain ⟨e, he⟩ := GlobalTheory.HWL.Rational.vec hG I hW (p * q)
    (fun a b => A (σ a).1 (σ b).1 * C (σ b).2 (σ a).2)
    (fun a => U (σ a).1 (σ a).2) (fun a => hU _ _) (fun a => ⟨_,
      GlobalTheory.HWL.Rational.matrix_eq (I.ioE : R.EE →+* RW LL) (φRW LL : RW LL →+* RW LL)
        A A' C Y U hC h σ a⟩) (σ.symm (i, j))
  rw [σ.apply_symm_apply] at he
  exact ⟨e, he.symm⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRings
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.FontaineTied

theorem fontCore_all_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.fontCore (P.PD K) :=
  fun l _ P AI hT K => GlobalTheory.Per.FontaineAll.fontCore_of_tied l P AI hT K

end GlobalTheory.Per.FontaineTied
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRingsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_extends_to_ainf_disc_rings : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X)) ∧ ∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l, ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G := by
  first | exact @GlobalTheory.BSP.galois_discMap | exact GlobalTheory.BSP.galois_discMap | (intros; apply GlobalTheory.BSP.galois_discMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittApproxFrobeniusPerfectionStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisFixedTensorWitt_approx_frobeniusPerfection : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), ∀ y ∈ fixSub AI LL (Hinf K : Set (GQ l)), ∀ m : ℕ, ∃ (n : ℕ) (y0 : RW LL) (e : W.EE) (r : RW LL), (φRW LL)^[n] y0 = E.tie.ioE e + (l : RW LL) * r ∧ NearPi AI LL s m (y - y0) := by
  first | exact @GlobalTheory.DecomplDense.fixSub_approx_perfection | exact GlobalTheory.DecomplDense.fixSub_approx_perfection | (intros; apply GlobalTheory.DecomplDense.fixSub_approx_perfection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnRootsOfPrimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_apply_eq_of_pow_eq_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Prime π → ∀ (n : ℕ) (y z : Om l), y ^ n = ((π : ↥K.1) : Om l) → z ^ n = ((π : ↥K.1) : Om l) → 0 < n → ∃ g : ↥(GK K), (g : GQ l) y = z := by
  first | exact @GlobalTheory.galois_transitive_on_roots_of_prime | exact GlobalTheory.galois_transitive_on_roots_of_prime | (intros; apply GlobalTheory.galois_transitive_on_roots_of_prime <;> assumption)
end

