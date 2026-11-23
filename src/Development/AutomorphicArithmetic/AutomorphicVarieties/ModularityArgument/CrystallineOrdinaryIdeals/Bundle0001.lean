module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsCrOfFinset
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CrLocal

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

theorem qcont_map {X V W : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup W]
    [Module ℚ_[l] W] (f : V →ₗ[ℚ_[l]] W) {c : X → V} (hc : QCont l c) : QCont l fun x => f (c x) := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : ContinuousAdd W := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap f).comp hc

theorem qcont_add {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] {c d : X → V}
    (hc : QCont l c) (hd : QCont l d) : QCont l fun x => c x + d x := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact Continuous.add hc hd

theorem qcont_sum {X V ι : Type} [Fintype ι] [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] {c : ι → X → V}
    (hc : ∀ i, QCont l (c i)) : QCont l fun x => ∑ i, c i x := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact continuous_finsetSum _ fun i _ => hc i

theorem contAction_of_qcont {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V)
    (h : ∀ v, QCont l fun g => ρ g v) : ContAction ρ := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  have h' : ∀ v, Continuous fun g => ρ g v := fun v => by
    have := h v
    unfold QCont at this
    rwa [← eq_moduleTopology ℚ_[l] V] at this
  let b := Module.finBasis ℚ_[l] V
  have e : (fun p : G × V => ρ p.1 p.2) = fun p => ∑ i, b.coord i p.2 • ρ p.1 (b i) := by
    funext p
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr p.2, map_sum]
    simp only [map_smul, Basis.coord_apply]
  unfold ReciprocityTheory.Gal.ContAction
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((IsModuleTopology.continuous_of_linearMap (b.coord i)).comp continuous_snd).smul ((h' _).comp continuous_fst)

theorem qcont_colRep {B : Type} [CommRing B] [Algebra ℚ_[l] B] (ρ : G →* GL (Fin 3) B)
    (h : ∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j) (v : Fin 3 → B) :
    QCont l fun g => resCoef ℚ_[l] (colRep ρ) g v := by
  have e : (fun g => resCoef ℚ_[l] (colRep ρ) g v) = fun g => ∑ i, ∑ j,
      ((LinearMap.single ℚ_[l] (fun _ : Fin 3 => B) i).comp (LinearMap.mulRight ℚ_[l] (v j)))
        ((ρ g : Matrix (Fin 3) (Fin 3) B) i j) := by
    funext g
    ext k
    change (ρ g : Matrix (Fin 3) (Fin 3) B).mulVec v k = _
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  rw [e]
  exact qcont_sum fun i => qcont_sum fun j => qcont_map _ (h i j)

variable [IsTopologicalGroup G] {φ : G →* GQ l}

theorem cr_sub (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] W] (ρ : Representation ℚ_[l] G V)
    (σ : Representation ℚ_[l] G W) (hρ : ∀ v, QCont l fun g => ρ g v) (hσ : ∀ v, QCont l fun g => σ g v)
    (f : V →ₗ[ℚ_[l]] W) (hf : ∀ g x, f (ρ g x) = σ g (f x)) (hi : Function.Injective f) (h : IsCr φ σ) :
    IsCr φ ρ := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  haveI : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℚ_[l] W
  exact ((isCrys_isDR_sub_quot φ hφ ρ σ (contAction_of_qcont ρ hρ) (contAction_of_qcont σ hσ) f hf).1 hi).1 h

theorem cr_prod (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] W] (ρ : Representation ℚ_[l] G V)
    (σ : Representation ℚ_[l] G W) (hρ : ∀ v, QCont l fun g => ρ g v) (hσ : ∀ v, QCont l fun g => σ g v)
    (h : IsCr φ ρ) (h' : IsCr φ σ) : IsCr φ (ρ.prod σ) := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  haveI : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℚ_[l] W
  exact (isCrys_isDR_prod φ hφ ρ σ (contAction_of_qcont ρ hρ) (contAction_of_qcont σ hσ)).1 h h'

theorem exists_cr_of_finset (hφ : IsOpenEmbedding φ) {V ι : Type} [AddCommGroup V] [Module ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (N : ι → Set V)
    (h : ∀ i, ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
      (σ : Representation ℚ_[l] G W) (f : V →ₗ[ℚ_[l]] W), (∀ v, QCont l fun g => σ g v) ∧ IsCr φ σ ∧
      (∀ g x, f (ρ g x) = σ g (f x)) ∧ ∀ x, f x = 0 → x ∈ N i) (S : Finset ι) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
      (σ : Representation ℚ_[l] G W) (f : V →ₗ[ℚ_[l]] W), (∀ v, QCont l fun g => σ g v) ∧ IsCr φ σ ∧
      (∀ g x, f (ρ g x) = σ g (f x)) ∧ ∀ x, f x = 0 → ∀ i ∈ S, x ∈ N i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨PUnit, inferInstance, inferInstance, inferInstance, 1, 0, fun v => ?_, ?_,
      fun _ _ => Subsingleton.elim _ _, by simp⟩
    · exact @continuous_const _ _ _ (moduleTopology ℚ_[l] PUnit) v
    · unfold IsCr
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton, mul_zero]
  | insert a S _ ih =>
    obtain ⟨W, _, _, _, σ, f, h1, h2, h3, h4⟩ := ih
    obtain ⟨W', _, _, _, σ', f', h1', h2', h3', h4'⟩ := h a
    refine ⟨W × W', inferInstance, inferInstance, inferInstance, σ.prod σ', f.prod f', fun v => ?_,
      cr_prod hφ σ σ' h1 h1' h2 h2', fun g x => ?_, fun x hx i hi => ?_⟩
    · have := qcont_add (qcont_map (LinearMap.inl ℚ_[l] W W') (h1 v.1)) (qcont_map (LinearMap.inr ℚ_[l] W W') (h1' v.2))
      convert this using 2 with g
      ext <;> simp [Representation.prod]
    · ext <;> simp [Representation.prod, h3, h3']
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h4' x (congrArg Prod.snd hx)
      · exact h4 x (congrArg Prod.fst hx) i hi

theorem isCr_of_local : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (ρ : G →* GL (Fin 3) B), (∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j) → (∀ (B' : Type) [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra B B'] [IsScalarTower ℚ_[l] B B'], IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (algebraMap B B')).comp ρ))) → IsCr φ (colRep ρ) := by
  intro l _ G _ _ _ φ hφ B _ _ _ ρ hc h
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  obtain ⟨W, _, _, _, σ, f, h1, h2, h3, h4⟩ := exists_cr_of_finset hφ (resCoef ℚ_[l] (colRep ρ))
    (fun m : MaximalSpectrum B => {v | ∀ i, algebraMap B (Localization.AtPrime m.asIdeal) (v i) = 0})
    (fun m => by
      let a : B →ₗ[ℚ_[l]] Localization.AtPrime m.asIdeal :=
        (IsScalarTower.toAlgHom ℚ_[l] B (Localization.AtPrime m.asIdeal)).toLinearMap
      haveI : Module.Finite ℚ_[l] (Localization.AtPrime m.asIdeal) :=
        Module.Finite.of_surjective a (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
      refine ⟨Fin 3 → Localization.AtPrime m.asIdeal, inferInstance, inferInstance, inferInstance,
        resCoef ℚ_[l] (colRep ((Matrix.GeneralLinearGroup.map
          (algebraMap B (Localization.AtPrime m.asIdeal))).comp ρ)), a.compLeft (Fin 3),
        qcont_colRep _ fun i j => qcont_map a (hc i j), h _, fun g x => ?_, fun x hx i => congrFun hx i⟩
      ext k
      exact RingHom.map_mulVec (algebraMap B (Localization.AtPrime m.asIdeal)) _ x k) Finset.univ
  refine cr_sub hφ (resCoef ℚ_[l] (colRep ρ)) σ (qcont_colRep ρ hc) h1 f h3 ?_ h2
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  funext i
  exact eq_zero_of_localization _ fun J hJ => h4 x hx ⟨J, hJ⟩ (Finset.mem_univ _) i

end GlobalTheory.CrLocal
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsFiniteLocalLiftOfSaturatedIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_local_lift_of_saturated_ideal : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (J : Ideal R) (d : R), (l : R) ∣ d → (∀ a, d * a ∈ J → a ∈ J) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B), J ≤ RingHom.ker f → ∃ (B' : Type) (_ : CommRing B') (_ : IsLocalRing B') (_ : Algebra ℚ_[l] B') (_ : Module.Finite ℚ_[l] B') (_ : Algebra O B') (_ : Algebra ℤ_[l] B') (_ : IsScalarTower ℤ_[l] O B') (_ : IsScalarTower ℤ_[l] ℚ_[l] B') (f' : R →ₐ[O] B') (q : B' →ₐ[ℚ_[l]] B), J ≤ RingHom.ker f' ∧ (∀ a, q (f' a) = f a) ∧ ∀ b, f' d * b = 0 → q b = 0 := by
  intro l _ O _ _ R _ _ _ J d _ hreg B _ _ _ _ _ _ _ _ f hJf
  classical
  let M0 : Ideal R := (IsLocalRing.maximalIdeal B).comap f
  let RM := Localization.AtPrime M0
  have hgu : ∀ y : M0.primeCompl, IsUnit ((f : R →+* B) (y : R)) := by
    intro y
    have hy := Ideal.mem_primeCompl_iff.1 y.2
    by_contra h
    exact hy (show (y : R) ∈ M0 from (IsLocalRing.mem_maximalIdeal _).2 h)
  let g : RM →+* B := IsLocalization.lift (M := M0.primeCompl) (S := RM) (g := (f : R →+* B)) hgu
  have hg : ∀ r : R, g (algebraMap R RM r) = f r := fun r => IsLocalization.lift_eq hgu r
  let α : O →+* RM := (algebraMap R RM).comp (algebraMap O R)
  let ψ : ℤ_[l] →+* RM := α.comp (algebraMap ℤ_[l] O)
  have hfψ : ∀ y : ℤ_[l], g (ψ y) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] y) := by
    intro y
    show g (algebraMap R RM (algebraMap O R (algebraMap ℤ_[l] O y))) = _
    rw [hg, f.commutes, ← IsScalarTower.algebraMap_apply ℤ_[l] O B y,
      ← IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B y]
  have hψu : ∀ y : nonZeroDivisors ℤ_[l], IsUnit (ψ y) := by
    intro y
    have hy0 : algebraMap ℤ_[l] ℚ_[l] y ≠ 0 := by
      intro h
      exact nonZeroDivisors.coe_ne_zero y
        ((IsFractionRing.injective ℤ_[l] ℚ_[l]) (h.trans (map_zero _).symm))
    have hr : IsUnit (f (algebraMap O R (algebraMap ℤ_[l] O y))) := by
      rw [← hg]
      have := (isUnit_iff_ne_zero.2 hy0).map (algebraMap ℚ_[l] B)
      rw [← hfψ y] at this
      exact this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff RM M0 _).2
      (Ideal.mem_primeCompl_iff.2 (fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) hr))
  let φ : ℚ_[l] →+* RM := IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) (S := ℚ_[l]) hψu
  have hφ : ∀ y : ℤ_[l], φ (algebraMap ℤ_[l] ℚ_[l] y) = ψ y := fun y => IsLocalization.lift_eq hψu y
  have hgφ : g.comp φ = algebraMap ℚ_[l] B := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l])
    ext y
    simp only [RingHom.comp_apply, hφ, hfψ]
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  obtain ⟨N0, hN0⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).1 this
  have hmaxg : ∀ x ∈ IsLocalRing.maximalIdeal RM ^ N0, g x = 0 := by
    intro x hx
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M0 RM, ← Ideal.map_pow] at hx
    have hle : Ideal.map (algebraMap R RM) (M0 ^ N0) ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hg]
      have h1 : f r ∈ (M0 ^ N0).map f := Ideal.mem_map_of_mem f hr
      rw [Ideal.map_pow] at h1
      have h2 : (M0.map f) ^ N0 ≤ IsLocalRing.maximalIdeal B ^ N0 :=
        Ideal.pow_right_mono Ideal.map_comap_le N0
      have h3 := h2 h1
      rw [hN0, Submodule.zero_eq_bot, Ideal.mem_bot] at h3
      exact h3
    exact RingHom.mem_ker.1 (hle hx)
  let J' : Ideal RM := J.map (algebraMap R RM)
  have hJg : ∀ x ∈ J', g x = 0 := by
    intro x hx
    have hle : J' ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hg]
      exact RingHom.mem_ker.1 (hJf hr)
    exact RingHom.mem_ker.1 (hle hx)
  have hreg' : ∀ a : RM, algebraMap R RM d * a ∈ J' → a ∈ J' := by
    intro a ha
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective M0.primeCompl a
    simp only at ha ⊢
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mem_map_algebraMap_iff] at ha
    obtain ⟨t, ht, htJ⟩ := ha
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    refine ⟨t, ht, hreg _ ?_⟩
    rw [mul_left_comm]
    exact htJ
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (IsLocalRing.maximalIdeal RM)
    (Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)})
  have hkey : ∀ c : RM, algebraMap R RM d * c ∈ J' ⊔ IsLocalRing.maximalIdeal RM ^ (N0 + k) →
      g c = 0 := by
    intro c hc
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 hc
    have hx1 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        (IsLocalRing.maximalIdeal RM ^ (N0 + k)) • (⊤ : Submodule RM (RM ⧸ J')) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hjy, map_add (f := _),
        Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
      exact Ideal.mem_map_of_mem _ hy
    have hx2 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)} := by
      have : Ideal.Quotient.mk J' (algebraMap R RM d * c) =
          c • Ideal.Quotient.mk J' (algebraMap R RM d) := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm c]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have hx3 := hk (N0 + k) (by omega)
    have h5 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        IsLocalRing.maximalIdeal RM ^ (N0 + k - k) • (IsLocalRing.maximalIdeal RM ^ k • ⊤ ⊓
          Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)}) := by
      rw [← hx3]
      exact Submodule.mem_inf.2 ⟨hx1, hx2⟩
    rw [Nat.add_sub_cancel] at h5
    have hx4 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈ IsLocalRing.maximalIdeal RM ^ N0 •
        Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)} :=
      Submodule.smul_mono le_rfl inf_le_right h5
    obtain ⟨a, ha, hav⟩ := Submodule.mem_smul_span_singleton.1 hx4
    have hdiff : algebraMap R RM d * (c - a) ∈ J' := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mul_sub, map_sub, ← hav, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm a, sub_self]
    have hca : c - a ∈ J' := hreg' _ hdiff
    have hc : c = (c - a) + a := by ring
    rw [hc, map_add (f := _), hJg _ hca, hmaxg _ ha, add_zero]
  let I : Ideal RM := J' ⊔ IsLocalRing.maximalIdeal RM ^ (N0 + k)
  have hIg : ∀ x ∈ I, g x = 0 := by
    intro x hx
    obtain ⟨j, hj, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), hJg _ hj, hmaxg _ (Ideal.pow_le_pow_right (by omega) hy), add_zero]
  have hIne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : RM) ∈ I := by rw [h]; exact Submodule.mem_top
    have := hIg 1 h1
    simp at this
  haveI : Nontrivial (RM ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hIne
  haveI hloc : IsLocalRing (RM ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI aQ : Algebra ℚ_[l] (RM ⧸ I) := ((Ideal.Quotient.mk I).comp φ).toAlgebra
  letI aO : Algebra O (RM ⧸ I) := ((Ideal.Quotient.mk I).comp α).toAlgebra
  letI aZ : Algebra ℤ_[l] (RM ⧸ I) := ((Ideal.Quotient.mk I).comp ψ).toAlgebra
  haveI t1 : @IsScalarTower ℤ_[l] O (RM ⧸ I) _ aO.toSMul aZ.toSMul := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI t2 : IsScalarTower ℤ_[l] ℚ_[l] (RM ⧸ I) := IsScalarTower.of_algebraMap_eq (fun x => by
    show Ideal.Quotient.mk I (ψ x) = Ideal.Quotient.mk I (φ (algebraMap ℤ_[l] ℚ_[l] x))
    rw [hφ])
  let f' : R →ₐ[O] (RM ⧸ I) :=
    { (Ideal.Quotient.mk I).comp (algebraMap R RM) with commutes' := fun o => rfl }
  let q : (RM ⧸ I) →ₐ[ℚ_[l]] B :=
    { Ideal.Quotient.lift I g hIg with
      commutes' := fun c => by
        show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I (φ c)) = algebraMap ℚ_[l] B c
        rw [Ideal.Quotient.lift_mk]
        exact RingHom.congr_fun hgφ c }
  have hmaxQ : IsLocalRing.maximalIdeal (RM ⧸ I) ≤
      (IsLocalRing.maximalIdeal RM).map (Ideal.Quotient.mk I) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.mem_map_of_mem
    by_contra hy
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hx hy
    exact hx (hy.map _)
  have hnil : IsLocalRing.maximalIdeal (RM ⧸ I) ^ (N0 + k) = ⊥ := by
    rw [eq_bot_iff]
    calc IsLocalRing.maximalIdeal (RM ⧸ I) ^ (N0 + k)
        ≤ ((IsLocalRing.maximalIdeal RM).map (Ideal.Quotient.mk I)) ^ (N0 + k) :=
          Ideal.pow_right_mono hmaxQ _
      _ = (IsLocalRing.maximalIdeal RM ^ (N0 + k)).map (Ideal.Quotient.mk I) :=
          (Ideal.map_pow _ _ _).symm
      _ ≤ I.map (Ideal.Quotient.mk I) := Ideal.map_mono le_sup_right
      _ = ⊥ := Ideal.map_quotient_self I
  haveI hart : IsArtinianRing (RM ⧸ I) := by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
    exact ⟨N0 + k, by rw [hnil]; rfl⟩
  have hfin : Module.Finite ℚ_[l] (RM ⧸ I) := by
    haveI : Module.Finite ℚ_[l] ((RM ⧸ I) ⧸ Ring.jacobson (RM ⧸ I)) := by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      have hle : IsLocalRing.maximalIdeal (RM ⧸ I) ≤ (IsLocalRing.maximalIdeal B).comap q := by
        intro x hx
        rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have hx0 : x ^ (N0 + k) = 0 := by
          have := Ideal.pow_mem_pow hx (N0 + k)
          rw [hnil] at this
          exact (Ideal.mem_bot).1 this
        have := hu.pow (N0 + k)
        rw [← map_pow, hx0, map_zero] at this
        exact not_isUnit_zero this
      have hcomap : (IsLocalRing.maximalIdeal B).comap (q : (RM ⧸ I) →+* B) ≤
          IsLocalRing.maximalIdeal (RM ⧸ I) :=
        IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
      have hinj : Function.Injective (Ideal.quotientMap (IsLocalRing.maximalIdeal B)
          (q : (RM ⧸ I) →+* B) hle) := Ideal.quotientMap_injective' hcomap
      haveI : Module.Finite ℚ_[l] (B ⧸ IsLocalRing.maximalIdeal B) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[l] (IsLocalRing.maximalIdeal B)).toLinearMap
          (Ideal.Quotient.mkₐ_surjective ℚ_[l] (IsLocalRing.maximalIdeal B))
      exact Module.Finite.of_injective
        (Ideal.quotientMapₐ (IsLocalRing.maximalIdeal B) q hle).toLinearMap hinj
    exact IsSemiprimaryRing.finite_of_isArtinian ℚ_[l] (RM ⧸ I) (RM ⧸ I)
  refine ⟨RM ⧸ I, inferInstance, hloc, aQ, hfin, aO, aZ, t1, t2, f', q, ?_, ?_, ?_⟩
  · intro x hx
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk I (algebraMap R RM x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)
  · intro a
    show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I (algebraMap R RM a)) = f a
    rw [Ideal.Quotient.lift_mk, hg]
  · intro b hb
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I c) = 0
    rw [Ideal.Quotient.lift_mk]
    apply hkey
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankDualInvariantsScalarRepEqFinrankKerSmulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul : ∀ {G E B : Type} [Group G] [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] {N : Type} [AddCommGroup N] [Module B N] [Module E N] [IsScalarTower E B N] [Module.Finite E N] (χ : G →* Bˣ) (ε : G →* Eˣ) (ρ : Representation E G N), (∀ g x, ρ g x = (χ g : B) • x) → ∀ δ : B, Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) = Ideal.span {δ} → finrank E ↥(H0dual ε ρ) = finrank E ↥(LinearMap.ker ((LinearMap.lsmul B N δ).restrictScalars E)) := by
  intro G E B _ _ _ _ _ N _ _ _ _ _ χ ε ρ hρ δ hδ
  set L := (LinearMap.lsmul B N δ).restrictScalars E with hL
  have key : H0dual ε ρ = (LinearMap.range L).dualAnnihilator := by
    ext f
    have hmem : f ∈ H0dual ε ρ ↔ ∀ (g : G) (x : N), f (ρ g x) = (ε g : E) * f x := by
      unfold H0dual
      exact Iff.rfl
    rw [hmem, Submodule.mem_dualAnnihilator]
    let S : Ideal B :=
      { carrier := {b | ∀ x : N, f (b • x) = 0}
        add_mem' := fun {a b} ha hb x => by
          simp only [Set.mem_setOf_eq] at ha hb
          rw [add_smul, map_add (f := _), ha x, hb x, add_zero]
        zero_mem' := fun x => by simp
        smul_mem' := fun c b hb x => by
          simp only [Set.mem_setOf_eq] at hb
          rw [smul_eq_mul, mul_comm, mul_smul]
          exact hb _ }
    have hS : ∀ b, b ∈ S ↔ ∀ x : N, f (b • x) = 0 := fun b => Iff.rfl
    have hgen : ∀ g, (∀ x, f (ρ g x) = (ε g : E) * f x) ↔
        ((χ g : B) - algebraMap E B (ε g)) ∈ S := by
      intro g
      rw [hS]
      refine forall_congr' fun x => ?_
      rw [hρ, sub_smul, map_sub, algebraMap_smul, f.map_smul (ε g : E) x, smul_eq_mul, sub_eq_zero]
    constructor
    · intro h
      have hle : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) ≤ S := by
        rw [Ideal.span_le]
        rintro _ ⟨g, rfl⟩
        exact (hgen g).1 (h g)
      rw [hδ] at hle
      have hd : δ ∈ S := hle (Ideal.subset_span rfl)
      rintro _ ⟨x, rfl⟩
      exact hd x
    · intro h g
      rw [hgen]
      have hd : δ ∈ S := fun x => h _ ⟨x, rfl⟩
      have hle : Ideal.span {δ} ≤ S := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hd
      rw [← hδ] at hle
      exact hle (Ideal.subset_span ⟨g, rfl⟩)
  rw [key]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range L)
  have h2 := LinearMap.finrank_range_add_finrank_ker L
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SpanCharacterSubCyclotomicEqOfPositiveWeight
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CharCycIdeal

theorem isClosed_ideal {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [TopologicalSpace B]
    [IsModuleTopology ℚ_[l] B] (J : Ideal B) : IsClosed (J : Set B) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨f, hf, hJ⟩ := Submodule.exists_le_ker_of_notMem (p := J.restrictScalars ℚ_[l]) (v := x) hx
  have hc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  refine Filter.mem_of_superset ((isOpen_ne.preimage hc).mem_nhds (x := x) hf) fun y hy h => hy ?_
  exact hJ (x := y) h

theorem span_range_sub_cyc : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) = (if w = 1 then Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} else ⊤) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχ w hw hI σ hσ
  have hA : ∀ g : GQ l, (cycA l l B g : B) = algebraMap ℚ_[l] B (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun g =>
    IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B _
  split_ifs with h1
  · subst h1
    refine le_antisymm ?_ (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨σ, rfl⟩))
    set J := Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} with hJ
    have hε : Continuous fun g => (cycA l l B (φ g) : B) := by
      simp only [hA]
      have h0 : Continuous (algebraMap ℚ_[l] B) :=
        IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] B)
      have h2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
      exact h0.comp (h2.comp (Units.continuous_val.comp
        ((UpperTheory.V.Loc.cycFacts l l).1.comp hφ.continuous)))
    let q : Bˣ →* (B ⧸ J)ˣ := Units.map (Ideal.Quotient.mk J : B →* B ⧸ J)
    let H : Subgroup G := (q.comp χ).eqLocus (q.comp ((cycA l l B).comp φ))
    have hH : ∀ g, g ∈ H ↔ (χ g : B) - (cycA l l B (φ g) : B) ∈ J := fun g => by
      rw [← Ideal.Quotient.eq]
      exact Units.ext_iff
    have hcl : IsClosed (H : Set G) := by
      have : (H : Set G) = (fun g => (χ g : B) - (cycA l l B (φ g) : B)) ⁻¹' (J : Set B) := Set.ext hH
      rw [this]
      exact (isClosed_ideal (l := l) J).preimage (hχ.sub hε)
    have hle : (Iq l).comap φ ⊔ Subgroup.zpowers σ ≤ H := by
      refine sup_le (fun g hg => ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [hH, hI g hg, zpow_one, sub_self]
        exact J.zero_mem
      · rw [hH]
        exact Ideal.subset_span rfl
    have htop := Subgroup.topologicalClosure_minimal _ hle hcl
    rw [hσ] at htop
    rw [Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    exact (hH g).1 (htop (Subgroup.mem_top g))
  · obtain ⟨s, ⟨⟨g, rfl⟩, hg⟩, hs⟩ := ((UpperTheory.V.Loc.cycInertia l).2 φ.range hφ.isOpen_range).2
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, w = ((n + 2 : ℕ) : ℤ) := ⟨(w - 2).toNat, by omega⟩
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨g, rfl⟩) ?_
    show IsUnit ((χ g : B) - (cycA l l B (φ g) : B))
    rw [hI g hg, zpow_natCast, Units.val_pow_eq_pow_val, hA, ← map_pow, ← map_sub]
    refine IsUnit.map _ (Ne.isUnit fun h => hs ?_)
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨n + 1, n.succ_pos, ?_⟩
    have h2 : cyc l l (φ g) ^ (n + 2) = cyc l l (φ g) := by
      apply Units.ext
      apply Subtype.ext
      rw [Units.val_pow_eq_pow_val]
      push_cast
      exact sub_eq_zero.1 h
    rw [pow_succ] at h2
    exact mul_eq_right.1 h2

end GlobalTheory.CharCycIdeal
end

