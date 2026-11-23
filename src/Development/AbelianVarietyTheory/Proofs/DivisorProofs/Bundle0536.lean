module

public import Mathlib
public import GroundTheory.Brauer.Degree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
section
open Module Polynomial TensorProduct

namespace GlobalTheory.CentSep

theorem aeval_mem_span_pow {K S : Type} [Field K] [Ring S] [Nontrivial S] [Algebra K S] (x : S)
    (hx : IsIntegral K x) (q : K[X]) :
    aeval x q ∈ Submodule.span K (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ)) := by
  have hm := minpoly.monic hx
  rw [← aeval_modByMonic_eq_self_of_root (p := q) (minpoly.aeval K x)]
  have hne : minpoly K x ≠ 1 := by
    intro h
    have := minpoly.natDegree_pos hx
    rw [h, natDegree_one] at this
    exact lt_irrefl _ this
  have hlt := natDegree_modByMonic_lt q hm hne
  rw [aeval_eq_sum_range' hlt]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨j, Finset.mem_range.mp hj⟩, rfl⟩)

theorem centralizer_toSubmodule {K S : Type} [Field K] [Ring S] [Algebra K S] (g : S) :
    Subalgebra.toSubmodule (Subalgebra.centralizer K ({g} : Set S)) =
      LinearMap.ker (LinearMap.mulLeft K g - LinearMap.mulRight K g) := by
  ext y
  simp [Subalgebra.mem_centralizer_iff, sub_eq_zero]

theorem natDegree_minpoly_le_baseChange {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem centralizer_eq_adjoin : ∀ (F B : Type) [Field F] [Ring B] [Algebra F B]
    [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ g : B, (minpoly F g).Separable →
      (minpoly F g).natDegree = n → Subalgebra.centralizer F {g} = Algebra.adjoin F {g} := by
  intro F B _ _ _ _ _ _ n hB g hsep hdeg
  classical
  obtain ⟨k, hk0, hkB, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F B
  have hkn : k = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hkB.symm.trans hB)
  subst hkn
  set K := AlgebraicClosure F
  set x : K ⊗[F] B := (1 : K) ⊗ₜ[F] g with hx
  have hxi : IsIntegral K x := IsIntegral.of_finite K x

  have hxr : x = Algebra.TensorProduct.includeRight g := rfl
  have hdvd : minpoly K x ∣ (minpoly F g).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hxr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := natDegree_minpoly_le_baseChange K g hxi
  rw [hdeg] at hge
  have hle : (minpoly K x).natDegree ≤ k := by
    have hmap : (minpoly F g).map (algebraMap F K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr (minpoly.ne_zero (IsIntegral.of_finite F g))
    calc (minpoly K x).natDegree ≤ ((minpoly F g).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap
      _ = k := by rw [natDegree_map, hdeg]
  have hxdeg : (minpoly K x).natDegree = k := le_antisymm hle hge

  set N := e x with hN
  have hmN : minpoly K N = minpoly K x := minpoly.algEquiv_eq e x
  have hchar : N.charpoly = minpoly K x := by
    have hd : minpoly K N ∣ N.charpoly := minpoly.dvd K N (Matrix.aeval_self_charpoly N)
    rw [hmN] at hd
    have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hd
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hxdeg])
    rw [this, (Matrix.charpoly_monic N).leadingCoeff, C_1, one_mul]
  have hNsep : N.charpoly.Separable := by
    rw [hchar]
    exact (hsep.map).of_dvd hdvd

  have hCK : Subalgebra.toSubmodule (Subalgebra.centralizer K ({x} : Set (K ⊗[F] B))) ≤
      Submodule.span K (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ)) := by
    intro y hy
    have hy' : x * y = y * x :=
      (Subalgebra.mem_centralizer_iff K).mp hy x (Set.mem_singleton x)
    have hcomm : Commute (e y) N := by
      change e y * e x = e x * e y
      rw [← map_mul, ← map_mul, hy']
    obtain ⟨q, hq⟩ := _root_.GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute k N (e y) hNsep hcomm
    have : y = aeval x q := by
      apply e.injective
      rw [hq, hN, ← aeval_algHom_apply]
    rw [this]
    exact aeval_mem_span_pow x hxi q
  have hfinK : finrank K (Subalgebra.toSubmodule (Subalgebra.centralizer K ({x} : Set (K ⊗[F] B))))
      ≤ k := by
    calc _ ≤ finrank K (Submodule.span K
            (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ))) :=
          Submodule.finrank_mono hCK
      _ ≤ Fintype.card (Fin (minpoly K x).natDegree) := finrank_range_le_card _
      _ = k := by rw [Fintype.card_fin, hxdeg]

  have hbc := (GlobalTheory.BadCount.finrank_iInf_ker_baseChange F K B (K ⊗[F] B) Unit
    (TensorProduct.mk F K B 1) (TensorProduct.isBaseChange F B K)
    (fun _ => LinearMap.mulLeft F g - LinearMap.mulRight F g)
    (fun _ => LinearMap.mulLeft K x - LinearMap.mulRight K x)
    (fun _ v => by
      simp [hx, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub])).1
  rw [_root_.iInf_const, _root_.iInf_const] at hbc
  rw [← centralizer_toSubmodule, ← centralizer_toSubmodule] at hbc

  have hadj : Algebra.adjoin F ({g} : Set B) ≤ Subalgebra.centralizer F {g} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      ((Subalgebra.mem_centralizer_iff F).mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]))
  have hspan : Submodule.span F (Set.range fun j : Fin (minpoly F g).natDegree => g ^ (j : ℕ)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin F ({g} : Set B)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton g)) _
  have hfinS : k ≤ finrank F (Subalgebra.toSubmodule (Algebra.adjoin F ({g} : Set B))) := by
    calc k = Fintype.card (Fin (minpoly F g).natDegree) := by rw [Fintype.card_fin, hdeg]
      _ = finrank F (Submodule.span F
            (Set.range fun j : Fin (minpoly F g).natDegree => g ^ (j : ℕ))) :=
          (finrank_span_eq_card (linearIndependent_pow g)).symm
      _ ≤ _ := Submodule.finrank_mono hspan
  have heq := Submodule.eq_of_le_of_finrank_le
    (Subalgebra.toSubmodule.monotone hadj) (by rw [← hbc]; exact hfinK.trans hfinS)
  exact (Subalgebra.toSubmodule_injective heq).symm

end GlobalTheory.CentSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyStructureSheafCohomologyModelOfQuasiIso
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Transfer

theorem coneExact_baseChange_of_quasiIso {R R' : Type} [CommRing R] [CommRing R'] [inst : Algebra R R']
    {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C)
    (h : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    GlobalTheory.ConeExact (K := fun p => R' ⊗[R] K.X p) (C := fun p => R' ⊗[R] C.X p)
      (fun p => (K.d p (p + 1)).hom.baseChange R') (fun p => (C.d p (p + 1)).hom.baseChange R')
      (fun p => (φ.f p).hom.baseChange R') := by
  have key := (GlobalTheory.quasiIso_iff_coneExact _).1 h
  clear h
  generalize hf : algebraMap R R' = f at key
  have e : inst = f.toAlgebra := Algebra.algebra_ext _ _ (fun r => by rw [hf]; rfl)
  subst e
  exact key

variable {R : Type} [CommRing R] {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C)
  (R' : Type) [CommRing R'] [Algebra R R']

theorem dB_comm (i j : ℕ) (x : R' ⊗[R] K.X i) :
    dB C R' i j ((φ.f i).hom.baseChange R' x) = (φ.f j).hom.baseChange R' (dB K R' i j x) := by
  simp only [dB, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, φ.comm]

theorem dB_dB (L : CochainComplex (ModuleCat.{0} R) ℕ) (i j k : ℕ) (x : R' ⊗[R] L.X i) :
    dB L R' j k (dB L R' i j x) = 0 := by
  simp only [dB, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, L.d_comp_d,
    ModuleCat.hom_zero, LinearMap.baseChange_zero, LinearMap.zero_apply]

def cycMap (i j : ℕ) : LinearMap.ker (dB K R' i j) →ₗ[R'] LinearMap.ker (dB C R' i j) :=
  ((φ.f i).hom.baseChange R').restrict (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [dB_comm, hx, map_zero])

theorem cycMap_val (i j : ℕ) (z : LinearMap.ker (dB K R' i j)) :
    (cycMap φ R' i j z).1 = (φ.f i).hom.baseChange R' z.1 := rfl

theorem ext_comm {R'' : Type} [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'') (i : ℕ) (y : R' ⊗[R] K.X i) :
    (φ.f i).hom.baseChange R'' (ext α _ y) = ext α _ ((φ.f i).hom.baseChange R' y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [ext]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exact_comp {H : Type} [AddCommGroup H] [Module R' H] (i j k : ℕ)
    (θ : LinearMap.ker (dB C R' j k) →ₗ[R'] H) (hs : Function.Surjective θ)
    (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (dB C R' i j))
    (surj : ∀ c, dB C R' j k c = 0 → ∃ (c' : R' ⊗[R] C.X i) (k' : R' ⊗[R] K.X j),
      dB K R' j k k' = 0 ∧ dB C R' i j c' + (φ.f j).hom.baseChange R' k' = c)
    (inj : ∀ (k' : R' ⊗[R] K.X j) (c : R' ⊗[R] C.X i), dB K R' j k k' = 0 →
      (φ.f j).hom.baseChange R' k' = dB C R' i j c → k' ∈ LinearMap.range (dB K R' i j)) :
    Function.Surjective (θ.comp (cycMap φ R' j k)) ∧
      ∀ z, θ.comp (cycMap φ R' j k) z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' i j) := by
  refine ⟨fun x => ?_, fun z => ?_⟩
  · obtain ⟨z, rfl⟩ := hs x
    obtain ⟨c', k', hk', hsum⟩ := surj z.1 z.2
    have hm : dB C R' i j c' ∈ LinearMap.ker (dB C R' j k) := dB_dB R' C i j k c'
    have hz : z = cycMap φ R' j k ⟨k', hk'⟩ + ⟨_, hm⟩ := Subtype.ext (by
      rw [Submodule.coe_add, cycMap_val, ← hsum, add_comm])
    refine ⟨⟨k', hk'⟩, ?_⟩
    rw [LinearMap.comp_apply, hz, map_add (f := _), (hk ⟨_, hm⟩).2 ⟨c', rfl⟩, add_zero]
  · rw [LinearMap.comp_apply, hk, cycMap_val]
    constructor
    · rintro ⟨c, hc⟩
      exact inj z.1 c z.2 hc.symm
    · rintro ⟨b, hb⟩
      exact ⟨(φ.f i).hom.baseChange R' b, by rw [dB_comm, hb]⟩

end Transfer

theorem nonempty_model_of_quasiIso : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C), (∀ (S : Type) [CommRing S] [Algebra R S],
      QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R S)).mapHomologicalComplex _).map φ)) →
    Model s C → Nonempty (Model s K) := by
  intro R _ X s K C φ hq M
  have h0 : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
    show IsPullback (𝟙 X) s s (spMap (RingHom.id R))
    rw [Cris.spMap_id]; exact IsPullback.id_horiz s
  obtain ⟨e1, -⟩ := M.θ0_one h0
  obtain ⟨y, hy1, hy2⟩ := (coneExact_baseChange_of_quasiIso φ (hq R)).zero ((1 : R) ⊗ₜ[R] M.one) 0
    ((LinearMap.mem_ker.1 e1).trans (map_zero _).symm) (map_zero _)
  let oneK : K.X 0 := TensorProduct.lid R (K.X 0) y
  have hy : (1 : R) ⊗ₜ[R] oneK = y := by
    rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
  have hinj : ∀ {M : ModuleCat.{0} R} (a b : M), (1 : R) ⊗ₜ[R] a = (1 : R) ⊗ₜ[R] b → a = b := fun a b hab => by
    rw [← TensorProduct.lid_symm_apply, ← TensorProduct.lid_symm_apply] at hab
    exact (TensorProduct.lid R _).symm.injective hab
  have hφone : (φ.f 0).hom oneK = M.one := hinj _ _ (by
    rw [← LinearMap.baseChange_tmul, hy]; exact hy1)
  have hdone : (K.d 0 1).hom oneK = 0 := hinj _ _ (by
    rw [← LinearMap.baseChange_tmul, hy, TensorProduct.tmul_zero]; exact hy2)
  refine ⟨{
    θ0 := fun {R'} _ _ {X'} {s'} {ψ} h => (LinearEquiv.ofBijective (cycMap φ R' 0 1) ⟨?_, ?_⟩).trans (M.θ0 h)
    one := oneK
    θ0_one := ?_
    θ1 := fun {R'} _ _ {X'} {s'} {ψ} h => (M.θ1 h).comp (cycMap φ R' 1 2)
    θ2 := fun {R'} _ _ {X'} {s'} {ψ} h => (M.θ2 h).comp (cycMap φ R' 2 3)
    exact := ?_
    nat := ?_ }⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    exact Subtype.ext ((coneExact_baseChange_of_quasiIso φ (hq _)).inj z.1 (congrArg Subtype.val hz) z.2)
  · intro w
    obtain ⟨x, hx1, hx2⟩ := (coneExact_baseChange_of_quasiIso φ (hq _)).zero w.1 0
      ((LinearMap.mem_ker.1 w.2).trans (map_zero _).symm) (map_zero _)
    exact ⟨⟨x, hx2⟩, Subtype.ext hx1⟩
  · intro R' _ _ X' s' ψ h
    have e : (1 : R') ⊗ₜ[R] oneK ∈ LinearMap.ker (dB K R' 0 1) := by
      rw [LinearMap.mem_ker, dB, LinearMap.baseChange_tmul, hdone, TensorProduct.tmul_zero]
    obtain ⟨e', he'⟩ := M.θ0_one h
    refine ⟨e, fun T => ?_⟩
    have hc : cycMap φ R' 0 1 ⟨_, e⟩ = ⟨_, e'⟩ := Subtype.ext (by
      rw [cycMap_val, LinearMap.baseChange_tmul, hφone])
    show (M.θ0 h (cycMap φ R' 0 1 ⟨_, e⟩)).1 T = 1
    rw [hc]; exact he' T
  · intro R' _ _ X' s' ψ h
    have hc := coneExact_baseChange_of_quasiIso φ (hq R')
    obtain ⟨s1, k1, s2, k2⟩ := M.exact h
    have A := exact_comp φ R' 0 1 2 (M.θ1 h) s1 k1
      (fun c hc0 => by
        obtain ⟨c', k', h1, h2⟩ := hc.succ 0 c 0 (hc0.trans (map_zero _).symm) (map_zero _)
        exact ⟨c', k', h2, h1⟩)
      (fun k' c hk' hkc => by
        obtain ⟨x, -, hx⟩ := hc.zero c k' hkc.symm hk'
        exact ⟨x, hx⟩)
    have B := exact_comp φ R' 1 2 3 (M.θ2 h) s2 k2
      (fun c hc0 => by
        obtain ⟨c', k', h1, h2⟩ := hc.succ 1 c 0 (hc0.trans (map_zero _).symm) (map_zero _)
        exact ⟨c', k', h2, h1⟩)
      (fun k' c hk' hkc => by
        obtain ⟨c', k'', -, hx⟩ := hc.succ 0 c k' hkc.symm hk'
        exact ⟨k'', hx⟩)
    exact ⟨A.1, A.2, B.1, B.2⟩
  · intro R' _ _ X' s' ψ h R'' _ _ X'' s'' ψ' h' α χ w hχ
    obtain ⟨n1, n2⟩ := M.nat h h' α χ w hχ
    refine ⟨fun z z' hz => ?_, fun z z' hz => ?_⟩
    · show M.θ1 h' (cycMap φ R'' 1 2 z') = pullHO1 w (M.θ1 h (cycMap φ R' 1 2 z))
      exact n1 _ _ (by rw [cycMap_val, cycMap_val, hz, ext_comm])
    · show M.θ2 h' (cycMap φ R'' 2 3 z') = pullHO2 w (M.θ2 h (cycMap φ R' 2 3 z))
      exact n2 _ _ (by rw [cycMap_val, cycMap_val, hz, ext_comm])

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.FerrandPush

section One
variable {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]

theorem isHomeomorph : IsHomeomorph i :=
  isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩

def upOpen (U : Y₀.Opens) : Y₁.Opens := ⟨i '' (U : Set Y₀), (isHomeomorph i).isOpenMap _ U.2⟩

theorem preimage_upOpen (U : Y₀.Opens) : i ⁻¹ᵁ upOpen i U = U := by
  ext x
  change i x ∈ i '' (U : Set Y₀) ↔ x ∈ U
  exact (isHomeomorph i).injective.mem_set_image

theorem upOpen_preimage (V : Y₁.Opens) : upOpen i (i ⁻¹ᵁ V) = V := by
  ext y
  change y ∈ i '' (i ⁻¹' (V : Set Y₁)) ↔ y ∈ V
  rw [Set.image_preimage_eq _ i.surjective]
  rfl

theorem upOpen_mono : Monotone (upOpen i) := fun _ _ h ↦ Set.image_mono h

def res (U : Y₀.Opens) : Γ(Y₁, upOpen i U) ⟶ Γ(Y₀, U) :=
  i.appLE (upOpen i U) U (preimage_upOpen i U).ge

theorem res_naturality {U V : Y₀.Opens} (h : U ≤ V) :
    Y₁.presheaf.map (homOfLE (upOpen_mono i h)).op ≫ res i U =
      res i V ≫ Y₀.presheaf.map (homOfLE h).op := by
  simp only [res, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end One

section Two
variable {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁]
  [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂]

abbrev cone (U : Y₀.Opens) : PullbackCone (res i₁ U) (res i₂ U) :=
  CommRingCat.pullbackCone (res i₁ U) (res i₂ U)

def coneIsLimit (U : Y₀.Opens) : IsLimit (cone i₁ i₂ U) :=
  CommRingCat.pullbackConeIsLimit _ _

def fibMap {U V : Y₀.Opens} (h : U ≤ V) : (cone i₁ i₂ V).pt ⟶ (cone i₁ i₂ U).pt :=
  PullbackCone.IsLimit.lift (coneIsLimit i₁ i₂ U)
    ((cone i₁ i₂ V).fst ≫ Y₁.presheaf.map (homOfLE (upOpen_mono i₁ h)).op)
    ((cone i₁ i₂ V).snd ≫ Y₂.presheaf.map (homOfLE (upOpen_mono i₂ h)).op)
    (by rw [Category.assoc, Category.assoc, res_naturality i₁ h, res_naturality i₂ h,
      (cone i₁ i₂ V).condition_assoc])

@[reassoc (attr := simp)]
theorem fibMap_fst {U V : Y₀.Opens} (h : U ≤ V) : fibMap i₁ i₂ h ≫ (cone i₁ i₂ U).fst =
    (cone i₁ i₂ V).fst ≫ Y₁.presheaf.map (homOfLE (upOpen_mono i₁ h)).op :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem fibMap_snd {U V : Y₀.Opens} (h : U ≤ V) : fibMap i₁ i₂ h ≫ (cone i₁ i₂ U).snd =
    (cone i₁ i₂ V).snd ≫ Y₂.presheaf.map (homOfLE (upOpen_mono i₂ h)).op :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

def fib : Y₀.Opensᵒᵖ ⥤ CommRingCat.{0} where
  obj U := (cone i₁ i₂ U.unop).pt
  map f := fibMap i₁ i₂ f.unop.le
  map_id U := PullbackCone.IsLimit.hom_ext (coneIsLimit i₁ i₂ U.unop)
    (by simp [homOfLE_refl]) (by simp [homOfLE_refl])
  map_comp f g := PullbackCone.IsLimit.hom_ext (coneIsLimit i₁ i₂ _)
    (by simp [← Functor.map_comp]; rfl) (by simp [← Functor.map_comp]; rfl)

def fibπ : fib i₁ i₂ ⟶ Y₀.presheaf where
  app U := (cone i₁ i₂ U.unop).fst ≫ res i₁ U.unop
  naturality U V f := by
    change fibMap i₁ i₂ f.unop.le ≫ _ ≫ _ = _
    rw [fibMap_fst_assoc, res_naturality]
    rfl

def good : Set Y₀.Opens :=
  {U | IsAffineOpen U ∧ IsAffineOpen (upOpen i₁ U) ∧ IsAffineOpen (upOpen i₂ U)}

end Two

end GlobalTheory.FerrandPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullCupOfBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.PullbackCupProduct

open GlobalTheory.CatCoh

universe u v u' v' u'' v''

theorem pull_cup_of_bijective {R R' : Type} [CommRing R] [CommRing R']
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
    {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
    {F'' : C'' ⥤ CommAlgCat.{0} R'} (m : CoefMap σ F F'') (n : CoefMap (RingHom.id R') F' F'')
    (h1 : Function.Bijective n.pull1) (h2 : Function.Bijective n.pull2) (a b : H1 F) :
    (LinearEquiv.ofBijective n.pull2 h2).symm (m.pull2 (cup F a b)) =
      cup F' ((LinearEquiv.ofBijective n.pull1 h1).symm (m.pull1 a))
        ((LinearEquiv.ofBijective n.pull1 h1).symm (m.pull1 b)) := by
  have back : ∀ x, n.pull1 ((LinearEquiv.ofBijective n.pull1 h1).symm x) = x := fun x =>
    (LinearEquiv.ofBijective n.pull1 h1).apply_symm_apply x
  apply (LinearEquiv.ofBijective n.pull2 h2).injective
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, n.pullCohomologyTwo_cup, back, back, m.pullCohomologyTwo_cup]

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : AlgebraicGeometry.Scheme}
  {s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} {s' : X' ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} {σ : R →+* R'}
  {φ : X' ⟶ X}

theorem pullHO2_cup (h : φ ≫ s = s' ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) (a b : GlobalTheory.CechDR.HO1 s) :
    GlobalTheory.AbCoh.pullHO2 h (cup _ a b) = cup _ (GlobalTheory.CechDR.pullHO1 h a) (GlobalTheory.CechDR.pullHO1 h b) := by
  unfold GlobalTheory.AbCoh.pullHO2 GlobalTheory.CechDR.pullHO1 GlobalTheory.CechDR.pairResEquivO
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact pull_cup_of_bijective _ _ _ _ a b

theorem main : ∀ (R R' : Type) [inst : CommRing R] [inst_1 : CommRing R'] (X X' : AlgebraicGeometry.Scheme) (s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (s' : X' ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : CategoryTheory.CategoryStruct.comp φ s = CategoryTheory.CategoryStruct.comp s' (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ)), Function.Surjective (⇑(GlobalTheory.CechDR.pullHO1 h) : GlobalTheory.CechDR.HO1 s → GlobalTheory.CechDR.HO1 s') → GlobalTheory.AbCoh.WedgeO (GlobalTheory.CechDR.OAff s') → Function.Surjective (⇑(GlobalTheory.AbCoh.pullHO2 h) : GlobalTheory.AbCoh.HO2 s → GlobalTheory.AbCoh.HO2 s') := by
  intro R R' _ _ X X' s s' σ φ h hsurj hwedge
  obtain ⟨e, he⟩ := hwedge

  have key : ∀ x, ∀ r : R', ∃ z, GlobalTheory.AbCoh.pullHO2 h z = e (r • x) := by
    intro x
    have hx : x ∈ Submodule.span R' (Set.range (exteriorPower.ιMulti R' 2)) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      intro r
      obtain ⟨a, ha⟩ := hsurj (r • v 0)
      obtain ⟨b, hb⟩ := hsurj (v 1)
      refine ⟨cup _ a b, ?_⟩
      have hv : r • exteriorPower.ιMulti R' 2 v = exteriorPower.ιMulti R' 2 ![r • v 0, v 1] := by
        have hupd : (![r • v 0, v 1] : Fin 2 → _) = Function.update v 0 (r • v 0) := by
          funext i
          fin_cases i <;> simp
        rw [hupd, AlternatingMap.map_update_smul, Function.update_eq_self]
      rw [pullHO2_cup, ha, hb, hv, he]
    | zero =>
      intro r
      exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro r
      obtain ⟨z₁, h₁⟩ := hx r
      obtain ⟨z₂, h₂⟩ := hy r
      exact ⟨z₁ + z₂, by rw [map_add (f := _), h₁, h₂, smul_add, map_add (f := _)]⟩
    | smul c x _ hx =>
      intro r
      obtain ⟨z, hz⟩ := hx (r * c)
      exact ⟨z, by rw [hz, smul_smul]⟩
  intro y
  obtain ⟨z, hz⟩ := key (e.symm y) 1
  exact ⟨z, by rw [hz, one_smul, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.PullbackCupProduct
end
end

