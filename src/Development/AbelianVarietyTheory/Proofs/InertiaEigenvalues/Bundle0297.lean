module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedUnramifiedTowerBasis
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobeniusFixedBasis

variable {F K M : Type} [Field F] [Field K] [Algebra F K] [AddCommGroup M] [Module K M] [Module F M]
  [IsScalarTower F K M]

theorem isScalarTower_sub (E : IntermediateField F K) : IsScalarTower F E M :=
  ⟨fun q e m => by
    show ((q • e : E) : K) • m = q • ((e : K) • m)
    rw [IntermediateField.coe_smul, smul_assoc]⟩

theorem exists_tower_basis (E : IntermediateField F K) {r : ℕ} (bω : Module.Basis (Fin r) F E)
    (n : Type) [Fintype n] [DecidableEq n] (v : n × Fin r → M) (hv : LinearIndependent F v)
    (hst : ∀ e ∈ E, ∀ c, e • v c ∈ Submodule.span F (Set.range v)) :
    ∃ a : n → M, (∀ j, a j ∈ Submodule.span F (Set.range v)) ∧
      LinearIndependent F (fun jk : n × Fin r => ((bω jk.2 : E) : K) • a jk.1) ∧
      Submodule.span F (Set.range fun jk : n × Fin r => ((bω jk.2 : E) : K) • a jk.1) =
        Submodule.span F (Set.range v) := by
  haveI := isScalarTower_sub (M := M) E
  set V := Submodule.span F (Set.range v) with hVdef
  have hstab : ∀ e ∈ E, ∀ x ∈ V, e • x ∈ V := by
    intro e he x hx
    have hle : V ≤ V.comap ((LinearMap.lsmul K M e).restrictScalars F) := by
      rw [hVdef, Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      exact hst e he c
    exact hle hx
  let VE : Submodule E M :=
    { carrier := V
      add_mem' := fun hx hy => V.add_mem hx hy
      zero_mem' := V.zero_mem
      smul_mem' := fun e x hx => hstab (e : K) e.2 x hx }
  have hfinV : Module.finrank F V = Fintype.card n * r := by
    rw [hVdef, finrank_span_eq_card hv, Fintype.card_prod, Fintype.card_fin]
  let e1 : VE ≃ₗ[F] V :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfinVE : Module.finrank F VE = Fintype.card n * r := by
    rw [← hfinV]; exact e1.finrank_eq
  haveI : Module.Finite F V := by
    rw [hVdef]; exact FiniteDimensional.span_of_finite F (Set.finite_range v)
  haveI : Module.Finite F VE := Module.Finite.equiv e1.symm
  haveI : Module.Finite E VE := Module.Finite.of_restrictScalars_finite F E VE
  have hE : Module.finrank F E = r := by
    rw [Module.finrank_eq_card_basis bω, Fintype.card_fin]
  haveI : Module.Finite F E := Module.Finite.of_basis bω
  have hrpos : 0 < r := by
    rw [← hE]; exact Module.finrank_pos
  have htower := Module.finrank_mul_finrank F E VE
  rw [hE, hfinVE] at htower
  have hnE : Module.finrank E VE = Fintype.card n := by
    have : Module.finrank E VE * r = Fintype.card n * r := by rw [mul_comm]; exact htower
    exact Nat.eq_of_mul_eq_mul_right hrpos this
  let b : Module.Basis n E VE := (Module.finBasisOfFinrankEq E VE hnE).reindex (Fintype.equivFin n).symm
  let bt : Module.Basis (Fin r × n) F VE := bω.smulTower b
  let f : VE →ₗ[F] M := (VE.subtype).restrictScalars F
  have hf : Function.Injective f := Subtype.val_injective
  refine ⟨fun j => (b j : M), fun j => (b j).2, ?_, ?_⟩
  · have h1 : LinearIndependent F (f ∘ bt) := bt.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
    have h2 := h1.comp (Equiv.prodComm n (Fin r)) (Equiv.injective _)
    convert h2 using 1
    ext jk
    simp [bt, f, Module.Basis.smulTower_apply, ← algebraMap_smul K]
  · have hli : LinearIndependent F (fun jk : n × Fin r => ((bω jk.2 : E) : K) • (b jk.1 : M)) := by
      have h1 : LinearIndependent F (f ∘ bt) := bt.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
      have h2 := h1.comp (Equiv.prodComm n (Fin r)) (Equiv.injective _)
      convert h2 using 1
      ext jk
      simp [bt, f, Module.Basis.smulTower_apply, ← algebraMap_smul K]
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨jk, rfl⟩
      exact hstab _ (bω jk.2).2 _ (b jk.1).2
    · rw [finrank_span_eq_card hli, hfinV, Fintype.card_prod, Fintype.card_fin]

end GlobalTheory.FrobeniusFixedBasis

namespace GlobalTheory.FrobeniusFixedBasis

def frFixed (l : ℕ) [Fact l.Prime] (r : ℕ) : IntermediateField ℚ_[l] ↥(MaximalUnramifiedExtension l) where
  carrier := {c | fr l r c = c}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add (f := _), ha, hb]
  algebraMap_mem' := fun q => by
    show (frobUr l ^ r) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = _
    exact AlgHom.commutes _ q
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv₀, hx]

end GlobalTheory.FrobeniusFixedBasis

namespace GlobalTheory


open GlobalTheory.FrobeniusFixedBasis in
theorem exists_frFixed_tower_basis : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) →
    LinearIndependent ℚ_[l] ω → (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) →
    ∀ (M : Type) [AddCommGroup M] [Module ↥(MaximalUnramifiedExtension l) M] [Module ℚ_[l] M] [IsScalarTower ℚ_[l] ↥(MaximalUnramifiedExtension l) M] (n : Type)
      [Fintype n] [DecidableEq n] (v : n × Fin r → M), LinearIndependent ℚ_[l] v →
      (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c, e • v c ∈ Submodule.span ℚ_[l] (Set.range v)) →
      ∃ a : n → M, (∀ j, a j ∈ Submodule.span ℚ_[l] (Set.range v)) ∧
        LinearIndependent ℚ_[l] (fun jk : n × Fin r => ω jk.2 • a jk.1) ∧
        Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range v) := by
  intro l _ r ω hω hli hsp M _ _ _ _ n _ _ v hv hst
  let E := frFixed l r
  let ω' : Fin r → E := fun k => ⟨ω k, hω k⟩
  have hli' : LinearIndependent ℚ_[l] ω' := by
    apply LinearIndependent.of_comp (E.val.toLinearMap)
    exact hli
  have hsp' : ⊤ ≤ Submodule.span ℚ_[l] (Set.range ω') := by
    rintro ⟨c, hc⟩ _
    obtain ⟨a, ha⟩ := hsp c hc
    have : (⟨c, hc⟩ : E) = ∑ k, a k • ω' k := by
      apply Subtype.ext
      show c = ((∑ k, a k • ω' k : E) : ↥(MaximalUnramifiedExtension l))
      rw [ha]
      simp [ω']
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let bω : Module.Basis (Fin r) ℚ_[l] E := Module.Basis.mk hli' hsp'
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_tower_basis E bω n v hv (fun e he c => hst e he c)
  have hb : ∀ k, ((bω k : E) : ↥(MaximalUnramifiedExtension l)) = ω k := fun k => by
    simp [bω, ω', Module.Basis.mk_apply]
  simp only [hb] at ha2 ha3
  exact ⟨a, ha1, ha2, ha3⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentAdmissibleCocyclesResidue
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (Z1 H1)

namespace GlobalTheory.ResidueBound

theorem exists_residue (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [FaithfulSMul ℤ_[l] O] (lam : O) (h : Irreducible lam) :
    Finite (O ⧸ Ideal.span {lam}) ∧ ∃ (k : Type) (_ : Field k) (_ : Algebra O k), CharP k l ∧
      Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ lam ∣ x := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {lam} := h.maximalIdeal_eq
  have hl : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    have h1 : ((IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ Algebra.IsIntegral.isIntegral _
    have h2 := IsLocalRing.eq_maximalIdeal h1
    have h3 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    rw [← h2, Ideal.mem_comap, map_natCast] at h3
    exact h3
  have hloc : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  have hfin : Finite (IsLocalRing.ResidueField O) := by
    have : Finite (IsLocalRing.ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).toEquiv.symm
    exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[l])
  refine ⟨?_, IsLocalRing.ResidueField O, inferInstance, inferInstance, ?_, IsLocalRing.residue_surjective, fun x => ?_⟩
  · rw [← hm]; exact hfin
  · rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (IsLocalRing.residue O),
      IsLocalRing.residue_eq_zero_iff]
    exact hl
  · rw [← Ideal.mem_span_singleton, ← hm]
    exact IsLocalRing.residue_eq_zero_iff x

variable {O G k : Type} [CommRing O] [Group G] [Field k] [Algebra O k] {lam : O}

theorem exists_tensor_equiv {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (q : M →ₗ[O] N) (hq : Function.Surjective q) (hk : KerIs lam q) :
    ∃ φ : (M ⊗[O] (O ⧸ Ideal.span {lam})) ≃ₗ[O] N, ∀ m y, φ (m ⊗ₜ Ideal.Quotient.mk _ y) = y • q m := by
  have hN : ∀ x : N, lam • x = 0 := fun x => by
    obtain ⟨m, rfl⟩ := hq x
    rw [← map_smul]; exact (hk _).2 ⟨m, rfl⟩
  let f : (M ⊗[O] (O ⧸ Ideal.span {lam})) →ₗ[O] N := TensorProduct.lift ((cycMap hN).comp q)
  have hf : ∀ m y, f (m ⊗ₜ Ideal.Quotient.mk _ y) = y • q m := fun _ _ => rfl
  have h1 : ∀ x : M ⊗[O] (O ⧸ Ideal.span {lam}), ∃ m : M, x = m ⊗ₜ Ideal.Quotient.mk _ 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul m y =>
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨y • m, ?_⟩
      rw [TensorProduct.smul_tmul]
      congr 1
      change _ = Ideal.Quotient.mk _ (y * 1)
      rw [mul_one]
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, (TensorProduct.add_tmul _ _ _).symm⟩
  refine ⟨LinearEquiv.ofBijective f ⟨?_, fun x => ?_⟩, hf⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := h1 x
    rw [hf, one_smul] at hx
    obtain ⟨y, rfl⟩ := (hk m).1 hx
    rw [TensorProduct.smul_tmul]
    have : lam • Ideal.Quotient.mk (Ideal.span {lam}) 1 = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    rw [this, TensorProduct.tmul_zero]
  · obtain ⟨m, rfl⟩ := hq x
    exact ⟨m ⊗ₜ Ideal.Quotient.mk _ 1, by rw [hf, one_smul]⟩

theorem exists_ext (T : Ob k G) (z : G → Fin T.m → k) (hz : ∀ g h, z (g * h) = z g + T.ρ g (z h)) :
    ∃ (E : Ob k G) (e : ((Fin T.m → k) × k) ≃ₗ[k] (Fin E.m → k)), IsExt T E z ∧
      ∀ g v y, E.ρ g (e (v, y)) = e (T.ρ g v + y • z g, y) := by
  have hz1 : z 1 = 0 := by simpa using hz 1 1
  let π : Representation k G ((Fin T.m → k) × k) :=
    { toFun := fun g => ((T.ρ g).coprod (LinearMap.toSpanSingleton k _ (z g))).prod (LinearMap.snd k _ _)
      map_one' := by
        refine LinearMap.ext fun x => ?_
        simp [hz1]
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        simp [hz g h]
        abel }
  obtain ⟨E, e, he⟩ := exists_ob π
  have he' : ∀ g v y, E.ρ g (e (v, y)) = e (T.ρ g v + y • z g, y) := fun g v y => (he g (v, y)).symm
  refine ⟨E, e, ⟨?_, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e (0, 1), fun g x => ?_, ?_, ?_, fun g => ?_⟩, he'⟩
  · have := e.finrank_eq
    simpa using this.symm
  · simp [he']
  · exact e.injective.comp LinearMap.inl_injective
  · rintro ⟨x, hx⟩
    have := congrArg Prod.snd (e.injective hx)
    simp at this
  · rw [he']
    change _ = e (0, 1) + e (z g, 0)
    rw [← map_add (f := _)]
    simp

variable [TopologicalSpace G]

theorem linearIndependent_of_indepMod (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) {N : Type} [AddCommGroup N] [Module O N]
    (π : Representation O G N) (T : Ob k G) (φ : N ≃ₗ[O] (Fin T.m → k)) (hφ : ∀ g x, φ (π g x) = T.ρ g (φ x))
    {s : ℕ} (z : Fin s → ↥(Z1 π ⊤)) (hz : IndepMod lam fun a => (Submodule.Quotient.mk (z a) : H1 π ⊤)) :
    LinearIndependent k fun a => (cob T).mkQ fun g => φ ((z a : G → N) g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  choose x hx using fun a => hs (c a)
  rw [← hx, hk]
  refine hz x ?_ a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_smul, ← map_sum] at hc
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hc
  have h1 : ∑ a, x a • (Submodule.Quotient.mk (z a) : H1 π ⊤) = Submodule.Quotient.mk (∑ a, x a • z a) := by
    change ∑ a, x a • Submodule.mkQ _ (z a) = Submodule.mkQ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum]
  rw [h1, Submodule.Quotient.mk_eq_zero]
  refine ⟨φ.symm b, Submodule.mem_top, ?_⟩
  funext g
  apply φ.injective
  have h2 := congrFun hb g
  change φ (π g (φ.symm b) - φ.symm b) = _
  rw [map_sub, hφ, φ.apply_symm_apply]
  refine Eq.trans h2 ?_
  simp [← hx]

theorem exists_ext_Ea (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x)
    {M X : Type} [AddCommGroup M] [Module O M] [AddCommGroup X] [Module O X] (W : Representation O G M)
    (χ : G →* Oˣ) (T : Ob k G) (φ : (M ⊗[O] X) ≃ₗ[O] (Fin T.m → k))
    (hφ : ∀ g x, φ (twCoef W χ X g x) = T.ρ g (φ x)) (ha : ∀ x : X, lam ^ 1 • x = 0)
    (z : ↥(Z1 (twCoef W χ X) ⊤)) :
    ∃ (E : Ob k G) (e : ((M ⊗[O] X) × (O ⧸ Ideal.span {lam ^ 1})) ≃ₗ[O] (Fin E.m → k)),
      IsExt T E (fun g => φ ((z : G → M ⊗[O] X) g)) ∧
      ∀ g x, e (twistRep (Ea W χ ha z) χ⁻¹ g x) = E.ρ g (e x) := by
  obtain ⟨E, e, hE, he⟩ := exists_ext T (fun g => φ ((z : G → M ⊗[O] X) g)) (fun g h => by
    rw [cocycle_mul, map_add (f := _), hφ])
  have hker : Ideal.span {lam ^ 1} = LinearMap.ker (Algebra.linearMap O k) := by
    ext x
    rw [pow_one, Ideal.mem_span_singleton, ← hk]
    rfl
  let ψ : (O ⧸ Ideal.span {lam ^ 1}) ≃ₗ[O] k :=
    (Submodule.quotEquivOfEq _ _ hker).trans ((Algebra.linearMap O k).quotKerEquivOfSurjective hs)
  have hψ : ∀ y, ψ (Ideal.Quotient.mk _ y) = algebraMap O k y := fun _ => rfl
  refine ⟨E, (φ.prodCongr ψ).trans (e.restrictScalars O), hE, ?_⟩
  rintro g ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : twistRep (Ea W χ ha z) χ⁻¹ g (m, Ideal.Quotient.mk _ y) =
      (twCoef W χ X g m + y • (z : G → M ⊗[O] X) g, Ideal.Quotient.mk _ y) := by
    rw [twistRep_apply, Ea, twistRep_apply, smul_smul, extRep_apply]
    simp
  rw [h1]
  change e (φ _, ψ _) = E.ρ g (e (φ _, ψ _))
  rw [he, map_add (f := _), hφ, map_smul, hψ, algebraMap_smul]


omit [TopologicalSpace G] in
theorem exists_coef_equiv {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M)
    (χ : G →* Oˣ) (T : Ob k G) (q : M →ₗ[O] (Fin T.m → k)) (hq : Function.Surjective q) (hk : KerIs lam q)
    (he : ∀ σ x, q (twistRep W χ⁻¹ σ x) = T.ρ σ (q x)) :
    ∃ φ : (M ⊗[O] (O ⧸ Ideal.span {lam})) ≃ₗ[O] (Fin T.m → k),
      ∀ g x, φ (twCoef W χ (O ⧸ Ideal.span {lam}) g x) = T.ρ g (φ x) := by
  obtain ⟨φ, hφ⟩ := exists_tensor_equiv q hq hk
  refine ⟨φ, fun g x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y =>
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [coefRep_tmul, hφ, hφ, he, LinearMap.map_smul_of_tower]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem exists_independent_admissible_cocycles_residue {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    [Algebra O LL] [TopologicalSpace LL] {n r l : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (Γ : GalData G Qp LL O) (D : TopData n r) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) {R : RingPG k l} (F : DFun R n G) (M : ModTh F D)
    (q : ↥Γ.T₀.L.T →ₗ[O] (Fin M.T.m → k)) (hq : Function.Surjective q) (hker : KerIs Γ.lam q)
    (hqe : ∀ σ x, q (twistRep Γ.W₀ Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x))
    (hmod : ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
      (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
      (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L)
    (h0 : ∀ (a : ℕ) (ha : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ, Γ.lam ^ a • x = 0), 1 ≤ a →
      adm PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) =
        admAt PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) a ha)
    (s : ℕ) (c : Fin s → H1 (twCoef Γ.W₀ Γ.χ₁ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) ⊤)
    (hc : ∀ a, c a ∈ adm PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) (hi : IndepMod Γ.lam c) :
    ∃ z : Fin s → G → Fin M.T.m → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) ∧
      LinearIndependent k (fun a => (cob M.T).mkQ (z a)) := by
  obtain ⟨φ, hφ⟩ := exists_coef_equiv Γ.W₀ Γ.χ₁ M.T q hq hker hqe
  have ha : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ, Γ.lam ^ 1 • x = 0 := fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [h0 1 ha le_rfl] at hc
  choose z hz hadm using hc
  obtain rfl : c = fun a => Submodule.Quotient.mk (z a) := funext fun a => (hz a).symm
  refine ⟨_, fun a => ?_, linearIndependent_of_indepMod hs hk _ M.T φ hφ z hi⟩
  obtain ⟨E, e, hE, he⟩ := exists_ext_Ea hs hk Γ.W₀ Γ.χ₁ M.T φ hφ ha (z a)
  obtain ⟨L, hL⟩ := hmod E _ _ e (hadm a) he
  exact ⟨E, L, hE, hL⟩

theorem resBound_dsum : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P),
    S.Real → S.Lem0 S.Γ.W₀ → S.ResBound S.Γ.W₀ S.D.dsum := by
  intro hψ l _ P S hR h0 s c hc hi
  obtain ⟨⟨hdom, hdvr, hfr⟩, hfd, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hfinO : Module.Finite ℤ_[l] S.O :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥S.LL.1 ↥(integralClosure ℤ_[l] ↥S.LL.1)
  have hfa : FaithfulSMul ℤ_[l] S.O := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h1 : Function.Injective (algebraMap ℤ_[l] ↥S.LL.1) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥S.LL.1]
      exact (algebraMap ℚ_[l] ↥S.LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [IsScalarTower.algebraMap_eq ℤ_[l] S.O ↥S.LL.1, RingHom.coe_comp] at h1
    exact h1.of_comp
  obtain ⟨hst, -, hT1, hT2, hT3⟩ := S.hyp
  obtain ⟨hfin, k, _, _, hch, hs, hk⟩ := exists_residue l S.O S.Γ.lam hst.2.2.2.2.2
  obtain ⟨R, ι, hι, F, M, -, ⟨q, hq, hker, hqe⟩, hmod⟩ := hR k ⟨hs, hk⟩
  obtain ⟨z, hz, hli⟩ := exists_independent_admissible_cocycles_residue (P.PD S.K) S.emb S.Γ S.D hs hk F M q hq hker hqe hmod
    (@h0 (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK S.Γ) _ _ hfin).2.1 s c hc hi
  exact _root_.GlobalTheory.Models.AdmBound.main hψ F M ι hι hT1 hT2 hT3 s z hz hli

end GlobalTheory.ResidueBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.SplitFrobDense

theorem exists_conj_ne {R : Ranks} (H : Host R) :
    ∃ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) ∧ y - x ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : ∀ x : 𝓞 H.E, H.conj (x : H.E) = x := fun x => by
    have := hc x ⟨H.conj x, (RingOfIntegers.isIntegral_coe x).map (H.conj.toAlgHom.restrictScalars ℤ)⟩ rfl
    exact congrArg (fun z : 𝓞 H.E => (z : H.E)) (sub_eq_zero.1 this)
  have h2 : ∀ z : H.E, H.conj z = z := fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 H.E) z
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h1 a) (h1 b)
  have := H.isCMField_hostE
  refine IsTotallyComplex.complexEmbedding_not_isReal H.φ₀ (ComplexEmbedding.isReal_iff.2 ?_)
  ext z
  exact (H.conjE_apply H.φ₀ z).symm.trans (congrArg H.φ₀ (h2 z))

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal.inertiaDeg ℤ = 1) (x : 𝓞 E) : ∃ n : ℤ, x - n ∈ v.asIdeal := by
  have := v.isPrime
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hp := Nat.absNorm_under_prime v.asIdeal
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  rw [hv, pow_one] at h
  rw [h] at hp
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hc : Nat.card (𝓞 E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal :=
    (Ideal.absNorm_eq_natCard v.asIdeal).symm
  have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  have hm := mem_zmultiples_of_prime_card hc (g := (1 : 𝓞 E ⧸ v.asIdeal)) (g' := Ideal.Quotient.mk _ x)
    one_ne_zero
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hm
  refine ⟨n, Ideal.Quotient.eq.1 ?_⟩
  rw [← hn]
  simp

theorem frobDense : ∀ D : D7, GlobalTheory.TwSys.Cheb → FrobDense D := by
  classical
  intro D hC T hT
  rw [dense_iff_inter_open]
  rintro V hV ⟨g, hg⟩
  have : IsGalois D.host.E D.nd.Om := {}
  have hn : (fun u : G D.host.E D.nd.Om => u * g) ⁻¹' V ∈ nhds (1 : G D.host.E D.nd.Om) :=
    (hV.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal D.host.E D.nd.Om _).1 hn
  have hgal : IsGalois D.host.E L := {}
  obtain ⟨x, y, hxy, hne⟩ := exists_conj_ne D.host
  have f1 : {v : PlE D.host | v.asIdeal ∣ Ideal.span {y - x}}.Finite :=
    Ideal.finite_factors (by simpa using hne)
  obtain ⟨v, hv, hf, -, B, hB, -, σ, hσ, hU⟩ := hC D.host.E D.nd.Om L.fixingSubgroup L.fixingSubgroup_isOpen
    ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g (f1.toFinset ∪ hT.toFinset)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton,
    not_or] at hv
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨n, hx⟩ := exists_int_sub_mem v hf x
  have hsplit : IsSplitPl D.host v := by
    refine ⟨x - n, hx, fun z hz hzv => h1 ?_⟩
    have hz' : z = y - n := by
      apply RingOfIntegers.ext
      rw [hz]
      simp [hxy]
    have := v.asIdeal.sub_mem hzv hx
    rwa [hz', sub_sub_sub_cancel_right] at this
  have := hL hU
  simp only [Set.mem_preimage, inv_mul_cancel_right] at this
  exact ⟨σ, this, v, h2, hsplit, B, hB, hσ⟩

end GlobalTheory.SplitFrobDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceFormIntegralIffGoodCoeffStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_form_integral_iff_goodCoeff : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ lam : LL →ₗ[ℚ_[l]] ℚ_[l], ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a := by
  first | exact @GlobalTheory.GoodCoeff.exists_trace_form_integral_iff | exact GlobalTheory.GoodCoeff.exists_trace_form_integral_iff | (intros; apply GlobalTheory.GoodCoeff.exists_trace_form_integral_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepKerIsOpenStatement
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualRep_ker_isOpen : ∀ (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → IsOpen ((redF D i ρ).ker : Set (G D.host.E D.nd.Om)) := by
  first | exact @GlobalTheory.TypeLeaf.redF_ker_isOpen | exact GlobalTheory.TypeLeaf.redF_ker_isOpen | (intros; apply GlobalTheory.TypeLeaf.redF_ker_isOpen <;> assumption)
end

