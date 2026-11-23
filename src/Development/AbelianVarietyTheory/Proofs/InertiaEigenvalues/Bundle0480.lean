module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0445
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCycZEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.Cyc

theorem isCyc_map_cycZ (l : ℕ) [Fact l.Prime] :
    IsCyc ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
      (cycZ (F := ℚ_[l]) (Ω := Om l) l)) := by
  intro g m ζ hζ
  haveI : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Om l) := fun i =>
    ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨_, ?_, cyclotomicCharacter.spec l (n := m)
    (MulSemiringAction.toRingAut (GQ l) (Om l) g) ζ hζ⟩
  set z : ℤ_[l] := ((cycZ (F := ℚ_[l]) (Ω := Om l) l g : ℤ_[l]ˣ) : ℤ_[l]) with hz
  change ‖(z : ℚ_[l]) - (((PadicInt.toZModPow m z).val : ℕ) : ℚ_[l])‖ ≤ _
  have h : z - (((PadicInt.toZModPow m z).val : ℕ) : ℤ_[l]) ∈
      Ideal.span {(l : ℤ_[l]) ^ m} := by
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
      sub_self]
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 h
  rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this

theorem exists_inertia_cycZ_eq : ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ), ∃ σ : GQ l, (∀ x ∈ MaximalUnramifiedExtension l, σ x = x) ∧ cycZ (F := ℚ_[l]) (Ω := Om l) l σ = u := by
  intro l _ u
  have hχ := isCyc_map_cycZ l
  set χ := (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
      (cycZ (F := ℚ_[l]) (Ω := Om l) l) with hχdef
  have hu1 : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u
  have hs : IsClosed {g : GQ l | (χ g : ℚ_[l]) = ((u : ℤ_[l]) : ℚ_[l])} :=
    isClosed_eq hχ.continuous continuous_const
  have key := hs.isCompact.inter_iInter_nonempty
    (fun x : MaximalUnramifiedExtension l => ((IntermediateField.adjoin ℚ_[l] {(x : Om l)}).fixingSubgroup : Set (GQ l)))
    (fun x => by
      haveI := IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) (x : Om l))
      exact IntermediateField.fixingSubgroup_isClosed _)
    (fun t => by
      let S : Set (Om l) := (fun x : MaximalUnramifiedExtension l => (x : Om l)) '' (t : Set (MaximalUnramifiedExtension l))
      haveI : Finite S := (t.finite_toSet.image _).to_subtype
      let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] S,
        IntermediateField.finiteDimensional_adjoin
          (fun x _ => Algebra.IsIntegral.isIntegral x)⟩
      obtain ⟨g, hg, hgu⟩ := exists_chi_eq K χ hχ _ hu1
      refine ⟨g, hgu, Set.mem_iInter₂.2 fun x hx => ?_⟩
      refine (mem_fixingSubgroup_adjoin_iff _ g).2 ?_
      rintro y rfl
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        ⟨IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩, x.2⟩)
  obtain ⟨g, hgu, hg⟩ := key
  refine ⟨g, fun x hx => ?_, Units.ext (Subtype.ext hgu)⟩
  exact (mem_fixingSubgroup_adjoin_iff _ g).1 (Set.mem_iInter.1 hg ⟨x, hx⟩) x rfl

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLatticeBasisLocal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem lattice_basis_exists : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V), IsLatBasis T b := by
  intro l _ G _ _ LL T
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI hfr : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI := T.L.free
  haveI : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let e0 := Module.Free.chooseBasis ↥(OL LL) ↥T.L.T
  let e := e0.reindex (Fintype.equivFin _)
  let v : Fin (Fintype.card (Module.Free.ChooseBasisIndex ↥(OL LL) ↥T.L.T)) → T.V := fun i => (e i : T.V)
  have hliO : LinearIndependent ↥(OL LL) v := e.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ↥LL.1 v := (LinearIndependent.iff_fractionRing ↥(OL LL) ↥LL.1).1 hliO

  have hexp : ∀ (x : T.V) (hx : x ∈ T.L.T), x = ∑ i, (((e.repr ⟨x, hx⟩ i : ↥(OL LL)) : ↥LL.1)) • v i := by
    intro x hx
    have h1 := e.sum_repr ⟨x, hx⟩
    have h2 := congrArg (fun y : ↥T.L.T => (y : T.V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    conv_lhs => rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (algebraMap_smul ↥LL.1 (e.repr ⟨x, hx⟩ i) (v i)).symm
  have hsp : ⊤ ≤ Submodule.span ↥LL.1 (Set.range v) := by
    rw [← T.L.span]
    refine Submodule.span_le.2 fun x hx => ?_
    rw [hexp x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨_, Module.Basis.mk hli hsp, fun i => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (e i).2
  · have h3 : (Module.Basis.mk hli hsp).repr x = fun j => (((e.repr ⟨x, hx⟩ j : ↥(OL LL)) : ↥LL.1)) := by
      conv_lhs => rw [hexp x hx]
      simp_rw [← Module.Basis.mk_apply hli hsp]
      exact (Module.Basis.mk hli hsp).repr_sum_self _
    rw [h3]
    exact (e.repr ⟨x, hx⟩ i).2

end GlobalTheory.BaseCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRing
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.IntegralModelOverCoeff

open scoped Matrix

theorem exists_integral_conj {l : ℕ} [Fact l.Prime] {O Γ : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (a : ℕ) (ρ : Γ →* GL (Fin a) (Qbar l))
    (hc : Continuous fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)))
    (hK : ∀ g s t, ∃ x, ι x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t) :
    ∃ (r : Γ →* GL (Fin a) O) (Pm : GL (Fin a) (Qbar l)),
      ∀ g, mapRep (ι.comp (algebraMap O (FractionRing O))) r g = Pm⁻¹ * ρ g * Pm := by
  classical
  set K := FractionRing O
  choose f hf using hK
  have hιi : Function.Injective (ι.mapMatrix : Matrix (Fin a) (Fin a) K →+* Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro A B h
    ext s t
    exact ι.injective (congrFun (congrFun h s) t)
  have hM : ∀ g, ι.mapMatrix (Matrix.of (f g)) = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g; ext s t; exact hf g s t
  let ρ0 : Γ →* Matrix (Fin a) (Fin a) K :=
    { toFun := fun g => Matrix.of (f g)
      map_one' := hιi (by rw [hM, map_one, map_one, Units.val_one])
      map_mul' := fun g h => hιi (by rw [map_mul, hM, hM, hM, map_mul, Units.val_mul]) }
  let ρK : Γ →* GL (Fin a) K := ρ0.toHomUnits
  have hρK : ∀ g, ι.mapMatrix ((ρK g : GL _ _) : Matrix (Fin a) (Fin a) K) =
      ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) := fun g => hM g

  let Int : Set (Matrix (Fin a) (Fin a) (Qbar l)) := {M | ∀ s t, ‖M s t‖ ≤ 1}
  have hInt1 : (1 : Matrix (Fin a) (Fin a) (Qbar l)) ∈ Int := by
    intro s t
    by_cases h : s = t
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hIntMul : ∀ A B, A ∈ Int → B ∈ Int → A * B ∈ Int := by
    intro A B hA hB s t
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hA s k) (norm_nonneg _) (hB k t)
  have hIntOpen : IsOpen Int := by
    have : Int = ⋂ s, ⋂ t, (fun M : Matrix (Fin a) (Fin a) (Qbar l) => M s t) ⁻¹' Metric.closedBall 0 1 := by
      ext M; simp [Int]
    rw [this]
    exact isOpen_iInter_of_finite fun s => isOpen_iInter_of_finite fun t =>
      (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero).preimage (continuous_id.matrix_elem s t)
  let U : Subgroup Γ :=
    { carrier := {g | ((ρ g : GL _ _) : Matrix _ _ _) ∈ Int ∧ ((ρ g⁻¹ : GL _ _) : Matrix _ _ _) ∈ Int}
      one_mem' := by simp [hInt1]
      mul_mem' := by
        rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
        refine ⟨?_, ?_⟩
        · rw [map_mul, Units.val_mul]; exact hIntMul _ _ hg1 hh1
        · rw [mul_inv_rev, map_mul, Units.val_mul]; exact hIntMul _ _ hh2 hg2
      inv_mem' := by
        rintro g ⟨h1, h2⟩
        exact ⟨h2, by rwa [inv_inv]⟩ }
  have hUopen : IsOpen (U : Set Γ) :=
    (hIntOpen.preimage hc).inter (hIntOpen.preimage (hc.comp continuous_inv))
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUopen
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hUint : ∀ h ∈ U, ∀ i j, ((ρK h : GL _ _) : Matrix (Fin a) (Fin a) K) i j ∈ (algebraMap O K).range := by
    intro h hh i j
    rw [GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.mem_range_iff ι hι]
    have := congrFun (congrFun (hρK h) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this]
    exact hh.1 i j
  obtain ⟨P, hP⟩ := GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.exists_conj_integral (O := O) a ρK U hUint
  choose e he using hP
  have hai : Function.Injective ((algebraMap O K).mapMatrix :
      Matrix (Fin a) (Fin a) O →+* Matrix (Fin a) (Fin a) K) := by
    intro A B h
    ext s t
    exact IsFractionRing.injective O K (congrFun (congrFun h s) t)
  have hE : ∀ g, (algebraMap O K).mapMatrix (Matrix.of (e g)) =
      ((P * ρK g * P⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := by
    intro g; ext s t; exact he g s t
  let r0 : Γ →* Matrix (Fin a) (Fin a) O :=
    { toFun := fun g => Matrix.of (e g)
      map_one' := hai (by rw [hE, map_one, map_one, mul_one, mul_inv_cancel, Units.val_one])
      map_mul' := fun g h => hai (by
        rw [map_mul, hE, hE, hE, ← Units.val_mul, map_mul]
        congr 1
        group) }
  refine ⟨r0.toHomUnits, (Units.map (ι.mapMatrix : Matrix (Fin a) (Fin a) K →+* _).toMonoidHom P)⁻¹, fun g => ?_⟩
  ext1
  rw [inv_inv]
  show (ι.comp (algebraMap O K)).mapMatrix (Matrix.of (e g)) = _
  have : (ι.comp (algebraMap O K)).mapMatrix (Matrix.of (e g)) =
      ι.mapMatrix ((algebraMap O K).mapMatrix (Matrix.of (e g))) := by
    ext s t; rfl
  rw [this, hE, Units.val_mul, Units.val_mul, map_mul, map_mul, hρK]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [Units.coe_map_inv]
  rfl

end GlobalTheory.IntegralModelOverCoeff

namespace GlobalTheory.IntegralModelOverCoeff

open Formalism.MainNotions.SumRepresentations

theorem exists_integral_model_rep : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) (a : ℕ) (ρ : GE N →* GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ → (∀ g s t, ∃ x, A.iotaQ i x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) → ∃ (r : GE N →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))), ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  intro R H what₂ N A i a ρ hc hK
  exact exists_integral_conj (A.iotaQ i) (A.iotaQ_alg i) a ρ hc hK

end GlobalTheory.IntegralModelOverCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionFiniteExtensionQl
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.CoefRetraction

theorem exists_retraction (A K L : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ r : L →ₗ[K] K, r 1 = 1 ∧ ∀ x : L, IsIntegral A x → ∃ a : A, algebraMap A K a = r x := by
  classical
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.Free A (integralClosure A L) :=
    IsIntegralClosure.module_free A K L (integralClosure A L)
  have : Module.Finite A (integralClosure A L) :=
    IsIntegralClosure.finite A K L (integralClosure A L)
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A L) (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A K L (integralClosure A L)

  let b := Module.Free.chooseBasis A (integralClosure A L)
  let bL := b.localizationLocalization K (nonZeroDivisors A) L
  have hrepr : ∀ (z : integralClosure A L) i,
      bL.repr (algebraMap (integralClosure A L) L z) i = algebraMap A K (b.repr z i) :=
    fun z i => b.localizationLocalization_repr_algebraMap K (nonZeroDivisors A) L z i

  have hspan : (1 : A) ∈ Ideal.span (Set.range fun i => b.repr 1 i) := by
    obtain ⟨d, hd⟩ : ∃ d : A, Ideal.span (Set.range fun i => b.repr 1 i) = Ideal.span {d} :=
      ⟨Submodule.IsPrincipal.generator (Ideal.span (Set.range fun i => b.repr 1 i)),
        (Submodule.IsPrincipal.span_singleton_generator _).symm⟩
    have hdiv : ∀ i, ∃ e : A, e * d = b.repr 1 i := fun i => by
      have hi : b.repr 1 i ∈ Ideal.span (Set.range fun i => b.repr 1 i) :=
        Ideal.subset_span ⟨i, rfl⟩
      rw [hd] at hi
      exact Ideal.mem_span_singleton'.mp hi
    choose e he using hdiv
    set β : integralClosure A L := ∑ i, e i • b i with hβ
    have hdβ : d • β = 1 := by
      rw [hβ, Finset.smul_sum]
      conv_rhs => rw [← b.sum_repr 1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm, he i]
    have hL : algebraMap A L d * (β : L) = 1 := by
      have := congrArg (fun z : integralClosure A L => (z : L)) hdβ
      simpa [Algebra.smul_def] using this
    have hK : algebraMap K L (algebraMap A K d) * (β : L) = 1 := by
      rw [← IsScalarTower.algebraMap_apply]; exact hL
    have hd0 : algebraMap A K d ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hK; exact zero_ne_one hK
    have hint : IsIntegral A (algebraMap K L (algebraMap A K d)⁻¹) := by
      rw [map_inv₀, inv_eq_of_mul_eq_one_right hK]
      exact β.2
    have hint' : IsIntegral A (algebraMap A K d)⁻¹ :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L) (algebraMap K L).injective).mp hint
    obtain ⟨u, hu⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint'
    have hud : u * d = 1 := by
      apply IsFractionRing.injective A K
      rw [map_mul, hu, map_one, inv_mul_cancel₀ hd0]
    rw [hd, ← hud]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self d)
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hspan
  refine ⟨∑ i, algebraMap A K (a i) • bL.coord i, ?_, ?_⟩
  · have h1 : (1 : L) = algebraMap (integralClosure A L) L 1 := (map_one _).symm
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul]
    rw [h1]
    simp only [hrepr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one (algebraMap A K), ← ha, map_sum]
    simp only [map_mul]
  · intro x hx
    set z : integralClosure A L := ⟨x, show x ∈ integralClosure A L from hx⟩ with hz
    have hx' : x = algebraMap (integralClosure A L) L z := rfl
    refine ⟨∑ i, a i * b.repr z i, ?_⟩
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul]
    rw [hx']
    simp only [hrepr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul]

theorem exists_retraction_closure (R F K L : Type) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field K] [Algebra F K] [Algebra R K] [IsScalarTower R F K] [FiniteDimensional F K]
    [IsPrincipalIdealRing (integralClosure R K)]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ r : L →ₗ[K] K, r 1 = 1 ∧ ∀ x : L, IsIntegral R x → IsIntegral R (r x) := by
  have : IsScalarTower (integralClosure R K) K L := inferInstance
  have : IsFractionRing (integralClosure R K) K :=
    integralClosure.isFractionRing_of_finite_extension F K
  have : IsScalarTower R (integralClosure R K) L := IsScalarTower.of_algebraMap_eq fun y => by
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply (integralClosure R K) K L]
    rfl
  obtain ⟨r, hr1, hr⟩ := exists_retraction (integralClosure R K) K L
  refine ⟨r, hr1, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hr x (hx.tower_top)
  rw [← ha]
  exact a.2

theorem exists_integral_retraction : ∀ (l : ℕ) [Fact l.Prime] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1),
    ∃ r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ a x, r (incl hL a * x) = a * r x) ∧ r 1 = 1 ∧
      (∀ x ∈ OL LL', r x ∈ OL LL) := by
  intro l _ LL LL' hL
  letI : Algebra ↥LL.1 ↥LL'.1 := (incl hL).toRingHom.toAlgebra
  have hmap : ∀ y : ↥LL.1, algebraMap ↥LL.1 ↥LL'.1 y = incl hL y := fun _ => rfl
  have : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun q => by
    rw [hmap, AlgHom.commutes]
  have : IsScalarTower ℤ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun z => by
    rw [hmap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1, AlgHom.commutes]
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  have : FiniteDimensional ↥LL.1 ↥LL'.1 := FiniteDimensional.right ℚ_[l] ↥LL.1 ↥LL'.1
  have : IsPrincipalIdealRing (integralClosure ℤ_[l] ↥LL.1) := by
    obtain ⟨h, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    exact h.toIsPrincipalIdealRing
  obtain ⟨r, hr1, hr⟩ := exists_retraction_closure ℤ_[l] ℚ_[l] ↥LL.1 ↥LL'.1
  refine ⟨r.restrictScalars ℚ_[l], fun a x => ?_, hr1, fun x hx => hr x hx⟩
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, ← hmap, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.CoefRetraction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSubmoduleAllCharpolySeparableStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_submodule_all_charpoly_separable : ∀ {O K X : Type} [CommRing O] [IsDomain O] [Infinite O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite X] (t : ℕ) (M : Submodule O (X → Matrix (Fin t) (Fin t) K)) (a : X → Matrix (Fin t) (Fin t) K), (∀ x, (a x).charpoly.Separable ∨ ∃ s ∈ M, ∃ c : K, c ≠ 0 ∧ (c • s x).charpoly.Separable) → ∃ s ∈ M, ∀ x, (a x + s x).charpoly.Separable := by
  first | exact @GlobalTheory.SepGeneric.exists_separable | exact GlobalTheory.SepGeneric.exists_separable | (intros; apply GlobalTheory.SepGeneric.exists_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMemGaloisStableLatticeQl
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TContMul

variable {l : ℕ} [Fact l.Prime]

theorem exists_pow_smul_mem (LL : FinExt l) (T : QLat LL) (v : T.V)
    (hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V)) : ∃ n : ℕ, ((l : ↥LL.1) ^ n) • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice
  | exact _root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice
  | (apply _root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticePowerScalar.exists_pow_smul_mem_lattice ..)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V), ∃ n : ℕ, ∃ x ∈ T.L.T, x = ((l : ↥LL.1) ^ n) • v := by
  intro l _ LL T v
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  obtain ⟨n, hn⟩ := exists_pow_smul_mem LL T v hv
  exact ⟨n, _, hn, rfl⟩

end GlobalTheory.TContMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowFixingNormalOfNear
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.PowFixNear
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem main : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), Normal ℚ_[l] ↥F.1 → ∀ g : GQ l, (∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) → ∃ s : ℕ, ∀ x ∈ F.1, (g ^ l ^ s) x = x := by
  intro l _ F hF g hg
  haveI := F.2
  haveI : Normal ℚ_[l] ↥F.1 := hF
  have hpow : ∀ (i : ℕ) (x : Om l), x ∈ F.1 → x ≠ 0 → ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i x hx hx0
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hg x hx hx0
  have hst : ∀ (h : GQ l) (x : Om l), x ∈ F.1 → h x ∈ F.1 := by
    intro h x hx
    have e := AlgEquiv.restrictNormal_commutes h (↥F.1) ⟨x, hx⟩
    have e' : h x = (algebraMap (↥F.1) (Om l)) ((AlgEquiv.restrictNormal h (↥F.1)) ⟨x, hx⟩) := e.symm
    rw [e']
    exact ((AlgEquiv.restrictNormal h (↥F.1)) ⟨x, hx⟩).2
  set r := AlgEquiv.restrictNormalHom (F := ℚ_[l]) (K₁ := Om l) (↥F.1) with hr
  have hfin : IsOfFinOrder (r g) := isOfFinOrder_of_finite _
  set N := orderOf (r g) with hNdef
  have hN0 : N ≠ 0 := (hfin.orderOf_pos).ne'
  have hgN : ∀ x ∈ F.1, (g ^ N) x = x := by
    intro x hx
    have e := AlgEquiv.restrictNormal_commutes (g ^ N) (↥F.1) ⟨x, hx⟩
    have h1 : AlgEquiv.restrictNormal (g ^ N) (↥F.1) = 1 := by
      have := pow_orderOf_eq_one (r g)
      rw [← map_pow] at this
      exact this
    rw [h1] at e
    simpa using e.symm
  obtain ⟨s, N', hN', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 l (Fact.out : l.Prime).ne_one
  refine ⟨s, fun y hy => ?_⟩
  refine GlobalTheory.TameInertiaCyclic.fix_of_near F (g ^ l ^ s) (hst _) (fun x hx hx0 => hpow _ x hx hx0) hN' (fun x hx => ?_) y hy
  rw [← pow_mul, ← hNe]
  exact hgN x hx

end GlobalTheory.PowFixNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Hilbert90MatrixCoboundaryCharPFiniteLevelStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_matrix_coboundary_of_fixed_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∀ (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) R), (∀ g h i j, ρ g (M h i j) = M h i j) → (∀ h i j, M h i j ^ p ^ m = M h i j) → (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, M g = 1) → ∃ W : Matrix (Fin r) (Fin r) R, IsUnit W.det ∧ (∀ i j, W i j ^ p ^ m = W i j) ∧ ∀ g, M g * W.map (ρ g) = W := by
  first | exact @GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary | exact GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary | (intros; apply GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary <;> assumption)
end

