module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

section IntegralSpan

variable {l : ℕ} [Fact l.Prime]

theorem one_mem_filD_zero : (1 : Per.BdR l) ∈ Per.FilD l 0 := by
  have h0 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← map_one (algebraMap (Per.AinfP l) (Per.BdRp l)),
      GlobalTheory.RingIface.ev_alg, Ideal.Quotient.eq_zero_iff_mem]
    simp
  have h1 := GlobalTheory.RingIface.alg_mem_FilD_nat l h0
  rwa [map_one, Nat.cast_zero] at h1

theorem algebraMap_mem_filD_zero (u : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) u ∈ Per.FilD l 0 := by
  rw [← mul_one (algebraMap (Per.BdRp l) (Per.BdR l) u), ← Algebra.smul_def]
  exact Submodule.smul_mem _ u one_mem_filD_zero

theorem equivFinsuppOfBasisLeft_map_id {O B B' ι : Type} [CommRing O] [Algebra ℤ_[l] O]
    [CommRing B] [CommRing B'] [Algebra ℤ_[l] B] [Algebra ℤ_[l] B']
    [DecidableEq ι] (b : Module.Basis ι ℤ_[l] O) (g : B →ₐ[ℤ_[l]] B') (r : O ⊗[ℤ_[l]] B) (k : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (Algebra.TensorProduct.map (AlgHom.id O O) g r) k =
      g (TensorProduct.equivFinsuppOfBasisLeft b r k) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul o β => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem equivFinsuppOfBasisRight_map_id {O R R' M κ : Type} [CommRing O] [CommRing R] [CommRing R']
    [Algebra O R] [Algebra O R'] [AddCommGroup M] [Module O M]
    [DecidableEq κ] (b : Module.Basis κ O M) (f : R →ₐ[O] R') (w : R ⊗[O] M) (j : κ) :
    TensorProduct.equivFinsuppOfBasisRight b (TensorProduct.map f.toLinearMap LinearMap.id w) j =
      f (TensorProduct.equivFinsuppOfBasisRight b w j) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem mem_span_filD_zero_of_iotaO_eq {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    (C : GlobalTheory.MemLoc.Core l) (r : OB l O) (s : OD l O) (h : iotaO O C r = dRO l O s) :
    r ∈ Submodule.span O
      {u : OB l O | ∃ β : Per.Bcris l, C.ι β ∈ Per.FilD l 0 ∧ u = (1 : O) ⊗ₜ[ℤ_[l]] β} := by
  classical
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hr : r = (TensorProduct.equivFinsuppOfBasisLeft b r).sum fun k β => b k ⊗ₜ[ℤ_[l]] β := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hr, Finsupp.sum]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  have hk : C.ι (TensorProduct.equivFinsuppOfBasisLeft b r k) ∈ Per.FilD l 0 := by
    have h1 := equivFinsuppOfBasisLeft_map_id b (iotaZ C) r k
    have h2 := equivFinsuppOfBasisLeft_map_id b (bdRpToBdR l) s k
    have h3 : Algebra.TensorProduct.map (AlgHom.id O O) (iotaZ C) r =
        Algebra.TensorProduct.map (AlgHom.id O O) (bdRpToBdR l) s := h
    rw [h3, h2] at h1
    have h4 : C.ι (TensorProduct.equivFinsuppOfBasisLeft b r k) =
        algebraMap (Per.BdRp l) (Per.BdR l) (TensorProduct.equivFinsuppOfBasisLeft b s k) := h1.symm
    rw [h4]
    exact algebraMap_mem_filD_zero _
  have h5 : b k ⊗ₜ[ℤ_[l]] (TensorProduct.equivFinsuppOfBasisLeft b r k) =
      b k • ((1 : O) ⊗ₜ[ℤ_[l]] (TensorProduct.equivFinsuppOfBasisLeft b r k)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h5]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hk, rfl⟩)

end IntegralSpan

theorem mem_span_filD_zero_of_integral : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
    (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (w : TW (OB l O) T),
    TWincl (iotaO O C) T w ∈ LinearMap.range (TWincl (dRO l O) T) →
      w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T),
        C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ O K _ _ _ _ _ _ _ T C w hw
  classical
  obtain ⟨z, hz⟩ := hw
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  have hw' : w = (TensorProduct.equivFinsuppOfBasisRight bT w).sum fun j r => r ⊗ₜ[O] bT j := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hw', Finsupp.sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  have hj : iotaO O C (TensorProduct.equivFinsuppOfBasisRight bT w j) =
      dRO l O (TensorProduct.equivFinsuppOfBasisRight bT z j) := by
    rw [← equivFinsuppOfBasisRight_map_id, ← equivFinsuppOfBasisRight_map_id]
    exact (congrArg (fun y => TensorProduct.equivFinsuppOfBasisRight bT y j) hz).symm
  have hr := mem_span_filD_zero_of_iotaO_eq C _ _ hj
  have hm := Submodule.mem_map_of_mem (f := (TensorProduct.mk O (OB l O) ↥T.L.T).flip (bT j)) hr
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨u, ⟨β, hβ, rfl⟩, rfl⟩
  exact ⟨β, bT j, hβ, rfl⟩

end GlobalTheory.BKGal.HatVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNOfMapMemSaturated
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.KerSat


set_option maxHeartbeats 1600000 in
theorem mem_N_of_map_mem : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀ := by
  intro D HW F l _ K s LL h W E T₀ T₁ T₂ ι π h0 h1 h2 hses x hx
  have hex : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := by
    haveI := GlobalTheory.EtaleExact.finite_OL LL
    haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
    refine GlobalTheory.EtaleExact.exact_of_tie E (GlobalTheory.EtaleExact.map_ne_top_of_tie E ?_ ?_) T₀ T₁ T₂ ι π hses
    · rw [(D.loc l).PD_p K]
      exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL
    · rw [(D.loc l).PD_p K]
      exact GlobalTheory.EtaleExact.sep_RW LL
  have key := _root_.GlobalTheory.NL.FrobeniusMatrixUniqueness.main D HW F l K s LL h T₀ h0
  obtain ⟨hinj, hexact, hsurj⟩ : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := hex
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  haveI : Module.Flat (AA K LL) W.EE :=
    GlobalTheory.T.flat_over_product_power_series_ring _ _ W.EE ((D.loc l).PD K).p W.EE_π W.EE_complete W.EE_dense W.EE_sat
  have hbc : IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype :=
    GlobalTheory.T.isBaseChange_comap_of_exact_flat (AA K LL) W.EE _ _ _ (W.map ι) (W.map π) (W.N T₁) (W.N T₂) hinj hexact hsurj
      (W.N_base T₁ h1) (W.N_base T₂ h2) (fun y hy => W.map_N π h1 h2 y hy)
  have hcomp : ∀ z, W.map π (W.map ι z) = 0 := fun z => (hexact _).2 ⟨z, rfl⟩
  have hA : ∀ (a : AA K LL) (z : W.DD T₀), W.map ι (a • z) = a • W.map ι z := fun a z =>
    ((W.map ι).restrictScalars (AA K LL)).map_smul a z
  have hAπ : ∀ (a : AA K LL) (z : W.DD T₁), W.map π (a • z) = a • W.map π z := fun a z =>
    ((W.map π).restrictScalars (AA K LL)).map_smul a z
  have hπc : ∀ y : W.DD T₁, W.map π ((letπ : AA K LL) • y) = 0 → W.map π y = 0 := by
    intro y hy
    rw [hAπ, ← algebraMap_smul W.EE (letπ : AA K LL)] at hy
    exact (W.EE_π.smul_left_cancel).mp (hy.trans (smul_zero _).symm)
  have hγ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), W.γ T₀ y ∈
      (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) := by
    intro y hy
    show W.map ι (W.γD T₀ W.gam y) ∈ W.N T₁
    rw [W.map_γ]
    exact W.N_Γ T₁ W.gam _ hy
  have hγπ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), W.γ T₀ y - y ∈
      ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).map (smulA W T₀ letπ) := by
    intro y hy
    change W.map ι y ∈ W.N T₁ at hy
    obtain ⟨z, hz, hzeq⟩ := W.N_π T₁ W.gam _ hy
    have h3 : W.map π z = 0 := by
      apply hπc
      rw [← hzeq, map_sub, W.map_γ, hcomp, map_zero, sub_zero]
    obtain ⟨z₀, rfl⟩ := (hexact z).1 h3
    refine ⟨z₀, hz, ?_⟩
    apply hinj
    change W.map ι ((letπ : AA K LL) • z₀) = W.map ι (W.γD T₀ W.gam y - y)
    rw [hA, map_sub, W.map_γ, hzeq]
  have hφ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • W.φD T₀ y ∈
      (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) := by
    intro y hy
    obtain ⟨k, hk⟩ := W.N_φ T₁ _ hy
    refine ⟨k, ?_⟩
    show W.map ι (W.Q ^ k • W.φD T₀ y) ∈ W.N T₁
    rw [hA, W.map_φ]
    exact hk
  have hfree := GlobalTheory.T.wachKernel_intersection_free_of_baseChange D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hses hbc
  have hspan := GlobalTheory.T.wachKernel_mem_frobeniusSpan_after_Q_pow D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hses
  have heq := key _ hfree hbc hγ hγπ hφ hspan
  rw [← heq]
  exact hx

end GlobalTheory.NL.KerSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicTraceGeWhittakerDimensionGLn
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.MirabolicComparison

theorem tr_add {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f h : G → ℂ) :
    tr a (fun x => f x + h x) = tr a f + tr a h := by
  simp [tr, mul_add, Finset.sum_add_distrib]

theorem tr_mul_const {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f : G → ℂ) (c : ℂ) :
    tr a (fun x => f x * c) = tr a f * c := by
  simp only [tr, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem tr_tr_list_nat {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    (a : MonoidAlgebra ℂ G) (b : MonoidAlgebra ℂ H) (ha : a * a = a) (hb : b * b = b) :
    ∀ L : List ((G → ℂ) × (H → ℂ)), (∀ p ∈ L, IsChar p.1 ∧ IsChar p.2) →
      ∃ n : ℕ, tr a (fun x => tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) = n := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simp [tr]⟩
  | cons p L ih =>
    intro hL
    obtain ⟨m, hm⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    obtain ⟨n₁, hn₁⟩ := (_root_.GlobalTheory.GLq.trIdem G a p.1).1 ha (hL p (List.mem_cons_self ..)).1
    obtain ⟨n₂, hn₂⟩ := (_root_.GlobalTheory.GLq.trIdem H b p.2).1 hb (hL p (List.mem_cons_self ..)).2
    refine ⟨n₁ * n₂ + m, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    rw [show (fun x => tr b (fun y => p.1 x * p.2 y + (L.map fun p => p.1 x * p.2 y).sum)) =
        (fun x => p.1 x * tr b p.2 + tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) from by
      funext x
      rw [tr_add]
      congr 1
      simp only [tr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring]
    rw [tr_add, tr_mul_const, hm, hn₁, hn₂]
    push_cast
    ring

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, _, hV⟩ := h
  exact ⟨V, hV⟩

theorem wh_der_nat (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N i : ℕ) (hi : i ≤ N)
    (χ : Gn g N → ℂ) (hχ : IsChar χ) : ∃ n : ℕ, wh ψ (der ψ i χ) = n := by
  obtain ⟨L, hL, hLeq⟩ := (_root_.GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp g i (N - i) N (by omega)).2 χ hχ
  have hres : (fun h : Gn g i => wh ψ (res i (N - i) χ h)) =
      fun h => tr (eU g (N - i) ψ) (fun y => (L.map fun p => p.1 h * p.2 y).sum) := by
    funext h
    simp only [wh]
    congr 1
    funext y
    exact hLeq h y
  show ∃ n : ℕ, tr (eU g i ψ) (fun h => wh ψ (res i (N - i) χ h)) = n
  rw [hres]
  exact tr_tr_list_nat _ _ (_root_.GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField g i 0 0 ψ).1 (_root_.GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField g (N - i) 0 0 ψ).1 L
    (fun p hp => ⟨isChar_of_isIrr (hL p hp).1, isChar_of_isIrr (hL p hp).2⟩)

theorem wh_der_zero (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (χ : Gn g N → ℂ) :
    wh ψ (der ψ 0 χ) = wh ψ χ := by
  haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (eU g 0 ψ).coeff 1 = 1 := by
    rw [(_root_.GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField g 0 0 0 ψ).2.1]; simp
  have hres : res 0 (N - 0) χ 1 = χ := by
    funext y
    change Gn g N at y
    simp only [res, Nat.zero_mul, pow_zero, inv_one, one_mul]
    rw [Finset.sum_eq_single y]
    · have : InPar 0 ((y : Gn g N) : Mt g N) ∧ tl 0 ((y : Gn g N) : Mt g N) = ((1 : Gn g 0) : Mt g 0) ∧
          br 0 (N - 0) ((y : Gn g N) : Mt g N) = ((y : Gn g (N - 0)) : Mt g (N - 0)) := by
        refine ⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩
        funext i j
        simp [br, entN]
      rw [if_pos this]
    · intro x _ hx
      rw [if_neg]
      rintro ⟨_, _, hb⟩
      apply hx
      apply Units.ext
      rw [← hb]
      funext i j
      simp [br, entN]
    · intro h; exact absurd (Finset.mem_univ _) h
  show tr (eU g 0 ψ) (fun h => wh ψ (res 0 (N - 0) χ h)) = wh ψ χ
  simp only [tr]
  rw [Fintype.sum_subsingleton _ 1, h1, one_mul, hres]

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

theorem mirabolic_comparison : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ),
    N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ →
      ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  intro g _ ψ hψ N k s hN hk χ hχ
  have hcl := isClass_of_isChar hχ
  rw [GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN χ hcl, _root_.GlobalTheory.GLq.ExactMult.tr_eJ'_eq_sum_wh_der g ψ hψ N k hk (by omega) χ hcl]
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_lt.le
  have hterm : ∀ i a b, (wh ψ (der ψ i χ) * ((g : ℂ) ^ a - (g : ℂ) ^ b)).re =
      (wh ψ (der ψ i χ)).re * ((g : ℝ) ^ a - (g : ℝ) ^ b) := by
    intro i a b
    rw [show ((g : ℂ) ^ a - (g : ℂ) ^ b) = (((g : ℝ) ^ a - (g : ℝ) ^ b : ℝ) : ℂ) by push_cast; ring]
    exact Complex.re_mul_ofReal _ _
  have hnn : ∀ i, i ≤ N → 0 ≤ (wh ψ (der ψ i χ)).re := by
    intro i hi
    obtain ⟨n, hn⟩ := wh_der_nat g ψ N i hi χ hχ
    rw [hn]
    simp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', Complex.add_re, Complex.add_re, Complex.re_sum, hterm 0, wh_der_zero]
  have hrest : 0 ≤ ∑ i ∈ Finset.range k', (wh ψ (der ψ (i + 1) χ) *
      ((g : ℂ) ^ (k' + 1 - (i + 1)) - (g : ℂ) ^ (k' + 1 - (i + 1) - 1))).re := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hterm]
    apply mul_nonneg (hnn _ (by omega))
    rw [sub_nonneg]
    exact pow_le_pow_right₀ hg1 (by omega)
  have hlast := hnn (k' + 1) (by omega)
  have h0 : (wh ψ χ).re * ((g : ℝ) ^ (k' + 1 - 0) - (g : ℝ) ^ (k' + 1 - 0 - 1)) =
      ((g : ℝ) ^ (k' + 1) - (g : ℝ) ^ (k' + 1 - 1)) * (wh ψ χ).re := by
    simp only [Nat.sub_zero]
    ring
  linarith

end GlobalTheory.GLq.MirabolicComparison
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantEqUnramifiedMulPeriod
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem phiB_moore_det {l : ℕ} [Fact l.Prime] (P : LocPrime l) (n : ℕ) (a : Fin (n + 1) → P.R.B)
    (ha : ∀ j, P.φB^[n + 1] (a j) = (l : P.R.B) * a j) :
    P.φB (Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j)).det =
      (-1) ^ n * (l : P.R.B) * (Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j)).det := by
  set M := Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j) with hM
  have h1 : P.φB M.det = (M.map P.φB).det := by
    rw [AlgHom.map_det]; rfl
  have h2 : M.map P.φB = Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (l : P.R.B) else 1) *
      M.submatrix (finRotate (n + 1)) id := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.map_apply, Matrix.submatrix_apply, finRotate_apply, id]
    simp only [hM, Matrix.of_apply]
    rw [← Function.iterate_succ_apply' (f := P.φB)]
    by_cases hi : i = Fin.last n
    · subst hi
      simp [ha]
    · rw [if_neg hi, one_mul, Fin.val_add_one, if_neg hi]
  rw [h1, h2, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute, sign_finRotate]
  simp [Finset.prod_ite_eq']
  ring

theorem mooreDeterminant_eq_unramified_mul_period_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h → ∀ a : Fin h → P.R.B, (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) → (∀ (i : ℕ) j, ev P i (a j) ∈ Fil P 0) → (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ≠ 0 → P.ιB (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ∈ Fil P 1 → ∃ κ : ↥(MaximalUnramifiedExtension l), κ ≠ 0 ∧ (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ * P.tB := by
  intro l _ P AI T h hh a ha _ hd hF
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  set d := (Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j)).det with hdd
  have hφd : P.φB d = (-1) ^ n * (l : P.R.B) * d := phiB_moore_det P n a ha
  have ht : IsUnit P.tB := isUnit_tB P
  have hl : IsUnit (l : P.R.B) := by
    have h0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have := (IsUnit.mk0 _ h0).map (algebraMap ℚ_[l] P.R.B)
    rwa [map_natCast] at this
  have hφt : P.φB P.tB = (l : P.R.B) * P.tB := by
    rw [localPrime_frobenius_periodT, Algebra.smul_def, map_natCast]
  set c := d * ((ht.unit⁻¹ : P.R.Bˣ) : P.R.B) with hc
  have hct : c * P.tB = d := by
    rw [hc, mul_assoc, Units.inv_mul_of_eq ht.unit_spec, mul_one]
  have hφc : P.φB c = (-1) ^ n * c := by
    apply (hl.mul ht).mul_right_cancel
    have e := congrArg P.φB hct
    rw [map_mul, hφt, hφd, ← hct] at e
    rw [show P.φB c * ((l : P.R.B) * P.tB) = P.φB c * ((l : P.R.B) * P.tB) from rfl]
    linear_combination e
  have hφ2 : P.φB^[2] c = c := by
    rw [Function.iterate_succ_apply', Function.iterate_one, hφc, map_mul, hφc, map_pow, map_neg, map_one, ← mul_assoc,
      ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have hFc : P.ιB c ∈ Fil P 0 := by
    have e : tz P 1 * P.ιB c = P.ιB d := by
      rw [show tz P 1 = P.ιB P.tB by simp [tz], ← map_mul, mul_comm, hct]
    have key := (_root_.GlobalTheory.PMon.bdR_tied l P AI T).2.2.1 0 1 (P.ιB c)
    rw [zero_add, e] at key
    exact key.2 hF
  have hev : ∀ j < 2, ev P j c ∈ Fil P 0 := by
    intro j hj
    interval_cases j
    · simpa [ev] using hFc
    · simp only [ev, Function.iterate_one, hφc, map_mul, map_pow, map_neg, map_one]
      rcases neg_one_pow_eq_or P.R.BdR n with h1 | h1
      · rw [h1, one_mul]; exact hFc
      · rw [h1, neg_one_mul]
        simp only [Fil, SetLike.mem_coe] at hFc ⊢
        exact neg_mem hFc
  obtain ⟨κ, -, hκ⟩ := _root_.GlobalTheory.PMon.unr_of_iterate_fixed l P AI T 2 two_pos c hφ2 hev
  refine ⟨κ, ?_, ?_⟩
  · rintro rfl
    apply hd
    rw [← hct, hκ, map_zero, zero_mul]
  · rw [← hκ, hct]

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMemCrystallinePrismDividedPowerFamilies
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem dpDen_mul_dvd_add (e i₁ i₂ n₁ n₂ : ℕ) :
    dpDen e i₁ n₁ * dpDen e i₂ n₂ ∣ dpDen e (i₁ + i₂) (n₁ + n₂) := by
  unfold dpDen
  have h1 := Nat.factorial_mul_factorial_dvd_factorial_add i₁ i₂
  have h2 : (n₁ / e).factorial * (n₂ / e).factorial ∣ ((n₁ + n₂) / e).factorial :=
    (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
      (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div n₁ n₂ e))
  have h3 := mul_dvd_mul h1 h2
  rwa [mul_mul_mul_comm] at h3

theorem mul_mem_QSet_of_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t x hx y hy
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨w', rfl⟩ := hy
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨fun p => ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ r ∈ Finset.HasAntidiagonal.antidiagonal p.2,
    ((dpDen e p.1 p.2 / (dpDen e q.1 r.1 * dpDen e q.2 r.2) : ℕ) : Wq l a) *
      (w (q.1, r.1) * w' (q.2, r.2)), ?_⟩
  funext τ
  ext i n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_ofW, Pi.mul_apply, coeff_mul, map_sum, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun q hq => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_mul, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [coeff_ofW, coeff_ofW]
  simp only [map_mul, map_natCast]
  have hd := dpDen_mul_dvd_add e q.1 q.2 r.1 r.2
  rw [Finset.HasAntidiagonal.mem_antidiagonal.1 hq, Finset.HasAntidiagonal.mem_antidiagonal.1 hr] at hd
  have h1 : (dpDen e q.1 r.1 : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  have h2 : (dpDen e q.2 r.2 : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  have h3 : (dpDen e i n : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  rw [Nat.cast_div hd (by push_cast; exact mul_ne_zero h1 h2)]
  push_cast
  field_simp

end GlobalTheory.CrysPrism
end
end

