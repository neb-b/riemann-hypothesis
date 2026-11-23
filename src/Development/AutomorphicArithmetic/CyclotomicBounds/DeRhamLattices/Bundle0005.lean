module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0004
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0020

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonToBSmulEqDeRhamAct
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem smul_abstract {Z O A B D M N : Type} [CommRing Z] [CommRing O] [CommRing A] [CommRing B]
    [CommRing D] [Algebra Z O] [Algebra Z A] [Algebra Z B] [Algebra Z D] [AddCommGroup M] [Module O M]
    [AddCommGroup N] (fB : O ⊗[Z] A →ₐ[O] O ⊗[Z] B) (fD : O ⊗[Z] A →ₐ[O] O ⊗[Z] D)
    (gB : A → B) (gD : A → D) (hB : ∀ o w, fB (o ⊗ₜ[Z] w) = o ⊗ₜ[Z] gB w)
    (hD : ∀ o w, fD (o ⊗ₜ[Z] w) = o ⊗ₜ[Z] gD w)
    (X : (O ⊗[Z] B) ⊗[O] M →+ N) (act : O ⊗[Z] D →+ (N →+ N))
    (h : ∀ (o o' : O) (w : A) (b : B) (x : M),
      X (((o * o') ⊗ₜ[Z] (gB w * b)) ⊗ₜ[O] x) = act (o ⊗ₜ[Z] gD w) (X ((o' ⊗ₜ[Z] b) ⊗ₜ[O] x)))
    (c : O ⊗[Z] A) (y : (O ⊗[Z] B) ⊗[O] M) : X (fB c • y) = act (fD c) (X y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' hc hc' => rw [map_add (f := _), add_smul, map_add (f := _), hc, hc', map_add (f := _), map_add (f := _), AddMonoidHom.add_apply]
  | tmul o w =>
    rw [hB, hD]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [smul_add, map_add (f := _), hy, hy', map_add (f := _), map_add (f := _)]
    | tmul r x =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add r r' hr hr' => rw [TensorProduct.add_tmul, smul_add, map_add (f := _), hr, hr', map_add (f := _), map_add (f := _)]
      | tmul o' b =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, h]

theorem _root_.UpperTheory.KN.crisComparison_toB_smul_eq_deRham_act :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (c : OA l ↥(OL LL)) (y : TW (OB l ↥(OL LL)) T), X (toB l ↥(OL LL) c • y) = act (toOD l ↥(OL LL) c) (X y) := by
  intro l _ LL T Pl AI Td X hX act hact c y
  refine smul_abstract (toB l ↥(OL LL)) (toOD l ↥(OL LL)) (fun w => acrisToBcris l (ainfToAcris l w))
    (fun w => ainfToBdRp l w) (fun _ _ => rfl) (fun _ _ => rfl) X act (fun o o' w b x => ?_) c y
  refine (hX _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg (act _) (hX o' b x)).symm
  refine Eq.trans ?_ (hact _ _ _ _).symm
  have h1 : ((o * o' : ↥(OL LL)) : ↥LL.1) = (o : ↥LL.1) * (o' : ↥LL.1) := rfl
  rw [h1, mul_smul, map_mul, UpperTheory.KN.crisComparison_ainf_eq_deRhamComparison l Pl AI Td w]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsBdRPlusCoeffsOfMemFilZeroDeRham
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem span_abs {Q Z O D B V κ : Type} [CommRing Q] [CommRing Z] [CommRing O] [CommRing D]
    [CommRing B] [Algebra Z O] [Algebra Z D] [Algebra Q B] [AddCommGroup V] [Module Q V] [Module O V]
    [Fintype κ] (T : Submodule O V) (b : Module.Basis κ O T) (F : Submodule Q B) (c : D →+* B)
    (act : O ⊗[Z] D →+ (V ⊗[Q] B →+ V ⊗[Q] B))
    (hact : ∀ (o : O) (d : D) (v : V) (e : B),
      act (o ⊗ₜ[Z] d) (v ⊗ₜ[Q] e) = (o • v) ⊗ₜ[Q] (c d * e))
    (hF : ∀ x ∈ F, ∃ y, x = c y)
    (hT : ∀ (v : V) (y : D), ∃ (q : Q) (x : T) (y1 : D), (x : V) = q • v ∧ c y = q • c y1)
    (f : V ⊗[Q] F →+ V ⊗[Q] B) (hf : ∀ (v : V) (x : F), f (v ⊗ₜ[Q] x) = v ⊗ₜ[Q] (x : B))
    (y : V ⊗[Q] F) :
    ∃ d : κ → O ⊗[Z] D, f y = ∑ k, act (d k) (((b k : T) : V) ⊗ₜ[Q] (1 : B)) := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a a' ha ha' =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨d', hd'⟩ := ha'
    refine ⟨d + d', ?_⟩
    rw [map_add (f := _), hd, hd', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, map_add (f := _), AddMonoidHom.add_apply]
  | tmul v x =>
    obtain ⟨y0, hy0⟩ := hF x x.2
    obtain ⟨q, t, y1, ht, hy⟩ := hT v y0
    refine ⟨fun k => b.repr t k ⊗ₜ[Z] y1, ?_⟩
    have h1 : (t : V) = ∑ k, b.repr t k • ((b k : T) : V) := by
      have h2 := congrArg T.subtype (b.sum_repr t).symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h2
      simpa only [map_smul, Submodule.subtype_apply] using h2
    rw [hf, hy0, hy, ← TensorProduct.smul_tmul, ← ht, h1, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hact, mul_one]

theorem _root_.UpperTheory.KN.exists_BdRPlus_coeffs_of_mem_filZero_deRham :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T), ∀ v : T.V ⊗[ℚ_[l]] Pl.R.BdR, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) → ∃ d : κ → OD l ↥(OL LL), v = ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ LL T Pl AI Td act hact κ _ b v hv
  obtain ⟨y, rfl⟩ := hv
  refine span_abs (Q := ℚ_[l]) (Z := ℤ_[l]) T.L.T b
    (((Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).Fil 0).restrictScalars ℚ_[l]) (GlobalTheory.BKGal.JumpDR.cD Td) act
    ?_ ?_ ?_ (AlgebraTensorModule.map (LinearMap.id : T.V →ₗ[↥LL.1] T.V)
      (((Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).Fil 0).restrictScalars ℚ_[l]).subtype).toAddMonoidHom ?_ y
  · intro o d v e
    refine (hact o d v e).trans ?_
    congr 1
    first | done | rfl | exact (algebraMap_smul (↥LL.1) o v)
  · intro x hx
    exact ((UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective l Pl AI Td (Formalism.MainNotions.ElementDenominator.qlExt l)).1 x).1 hx
  · intro v y
    obtain ⟨n, x, hx⟩ := UpperTheory.KN.exists_prime_pow_smul_mem_lattice l LL T v
    obtain ⟨z, hz⟩ := ((GlobalTheory.MemLoc.isUnit_l_BdRp l).pow n).exists_right_inv
    refine ⟨(l : ℚ_[l]) ^ n, x, z * y, hx, ?_⟩
    have h : y = ((l : ℕ) : Per.BdRp l) ^ n * (z * y) := by rw [← mul_assoc, hz, one_mul]
    conv_lhs => rw [h]
    rw [map_mul, map_pow, map_natCast, Algebra.smul_def, map_pow, map_natCast]
  · intro v x
    rfl
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeActionMemFilZeroDeRham
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.latticeAction_mem_filZero_deRham :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (d : OD l ↥(OL LL)) (v : T.V), act d (v ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) := by
  intro l _ LL T Pl AI Td act hact d v
  have hfil := (UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective l Pl AI Td (Formalism.MainNotions.ElementDenominator.qlExt l)).1
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul o b =>
    rw [hact, mul_one]
    have hb : (JumpDR.cD Td) b ∈ (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).Fil 0 := (hfil _).2 ⟨b, rfl⟩
    rw [FilV.eq_1]
    exact ⟨((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] ⟨_, hb⟩, by simp⟩
  | add x y hx hy =>
    rw [map_add (f := _), AddMonoidHom.add_apply]
    exact Submodule.add_mem _ hx hy
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LinearIndependentQlProductBasisOfZlLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem exists_sum_tmul {R O B σ : Type} [CommRing R] [AddCommGroup O] [Module R O]
    [AddCommGroup B] [Module R B] [Fintype σ] (ω : Module.Basis σ R O) (x : O ⊗[R] B) :
    ∃ y : σ → B, x = ∑ s, ω s ⊗ₜ[R] y s :=
  _root_.UpperTheory.Reformulated.B.Qj2.exists_sum_tmul ω x

private theorem abstract_indep {R K O B V C σ κ : Type} [CommRing R] [Field K] [AddCommGroup O]
    [Module R O] [AddCommGroup B] [Module R B] [AddCommGroup V] [Module K V] [AddCommGroup C]
    [Module K C] [Fintype σ] [Fintype κ] (ω : Module.Basis σ R O)
    (act : O ⊗[R] B →+ (V ⊗[K] C →+ V ⊗[K] C)) (e : κ → V ⊗[K] C) (w : σ × κ → V) (f : B → C)
    (hf : ∀ y, f y = 0 → y = 0) (hw : LinearIndependent K w)
    (hact : ∀ s k y, act (ω s ⊗ₜ[R] y) (e k) = w (s, k) ⊗ₜ[K] f y)
    (d : κ → O ⊗[R] B) (hd : ∑ k, act (d k) (e k) = 0) (k : κ) : d k = 0 := by
  choose y hy using fun k => exists_sum_tmul ω (d k)
  have h : ∑ p : σ × κ, w p ⊗ₜ[K] f (y p.2 p.1) = 0 := by
    rw [← hd, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy k, map_sum]
    have hsum (S : Finset σ) :
        (∑ s ∈ S, act (ω s ⊗ₜ[R] y k s)) (e k) =
          ∑ s ∈ S, act (ω s ⊗ₜ[R] y k s) (e k) := by
      classical
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih => simp [ha, ih]
    rw [hsum]
    exact Finset.sum_congr rfl fun s _ => (hact s k _).symm
  have h0 := UpperTheory.KN.coeff_eq_zero_of_sum_tmul_linearIndependent_eq_zero K V C (σ × κ) w hw _ h
  rw [hy k]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [hf _ (h0 (s, k)), TensorProduct.tmul_zero]

theorem _root_.UpperTheory.KN.linearIndependent_Ql_productBasis_of_Zl_lattice :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T), ∀ d : κ → OD l ↥(OL LL), ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) = 0 → ∀ k, d k = 0 := by
  intro l _ LL T Pl AI Td act hact κ _ b d hd k
  haveI : Module.Free ℤ_[l] ↥(OL LL) := inferInstance
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := inferInstance
  have hinj := (UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective l Pl AI Td LL).2
  refine abstract_indep (Module.Free.chooseBasis ℤ_[l] ↥(OL LL)) act
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) _
    (fun y => GlobalTheory.BKGal.JumpDR.cD Td y) (fun y hy => hinj (hy.trans (map_zero _).symm))
    (UpperTheory.KN.linearIndependent_Ql_integerBasis_smul_latticeBasis l LL T κ _ b (Module.Free.chooseBasis ℤ_[l] ↥(OL LL))) ?_ d hd k
  intro s k y
  refine (hact _ _ _ _).trans ?_
  rw [mul_one]
end

