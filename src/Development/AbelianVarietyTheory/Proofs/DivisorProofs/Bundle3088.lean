module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparatesOnSmoothOfPair
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.DeRhamCharpolyZero

open GlobalTheory.AV

theorem charpoly_of_bijective {R K M V : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (E : K ⊗[R] M →ₗ[K] V) (hE : Function.Bijective E) (φ : Module.End R M) (T : Module.End K V)
    (h : ∀ m, T (E (1 ⊗ₜ m)) = E (1 ⊗ₜ φ m)) : T.charpoly = φ.charpoly.map (algebraMap R K) := by
  let e := LinearEquiv.ofBijective E hE
  have hT : T = e.conj (φ.baseChange K) := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨z, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply]
    induction z with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x m =>
      have : x ⊗ₜ[R] m = x • ((1 : K) ⊗ₜ[R] m) := by simp [TensorProduct.smul_tmul']
      rw [this, map_smul, map_smul, map_smul, map_smul]
      exact congrArg (x • ·) (h m)
  rw [hT, LinearEquiv.charpoly_conj, LinearMap.charpoly_baseChange]

theorem charpoly_dualMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module.Finite K (Module.Dual K V)] (f : Module.End K V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis K V),
    ← LinearMap.charpoly_toMatrix f.dualMap (Module.finBasis K V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

theorem finite_prim {K : Type} [Field K] (B : AbVar K) : Module.Finite K (primDR B.X) :=
  (GlobalTheory.abelianDeRham.1.prim B.ab B.smooth).1

theorem finite_HdR {K : Type} [Field K] (B : AbVar K) : Module.Finite K (HdR B.X) :=
  haveI := finite_prim B
  inferInstance

theorem charpoly_push_of_pullback {K L : Type} [Field K] [Field L] [Algebra K L] (B₀ : AbVar K) (B : AbVar L)
    {φ : B.X.left ⟶ B₀.X.left} (h : IsGrpPullback B.X B₀.X (spMap (algebraMap K L)) φ) (f₀ : B₀ ⟶ B₀) (f : B ⟶ B)
    (e : φ ≫ f₀.hom.left = f.hom.left ≫ φ) [Module.Finite K (HdR B₀.X)] [Module.Finite L (HdR B.X)] :
    LinearMap.charpoly (push (dp0 L) (𝟙 _) f.hom) =
      (LinearMap.charpoly (push (dp0 K) (𝟙 _) f₀.hom)).map (algebraMap K L) := by
  haveI := finite_prim B₀
  haveI := finite_prim B
  have m := GlobalTheory.Published.AbelianDeRham.bcMor h
  have hm : m.IsBC := (GlobalTheory.abelianDeRham.2.2.1 K B₀.X B₀.dim B₀.ab B₀.smooth L B.X φ h).1
  have h1 : LinearMap.charpoly (push (dp0 L) (𝟙 _) f.hom) = (primPull (dp0 L) (𝟙 _) f.hom).charpoly :=
    charpoly_dualMap _
  have h2 : LinearMap.charpoly (push (dp0 K) (𝟙 _) f₀.hom) = (primPull (dp0 K) (𝟙 _) f₀.hom).charpoly :=
    charpoly_dualMap _
  rw [h1, h2]
  refine charpoly_of_bijective (liftSemi m.pull) hm _ _ fun c => ?_
  rw [liftSemi_tmul, liftSemi_tmul, one_smul, one_smul]
  have k := (homMor (dp0 K) (𝟙 _) f₀.hom).comp m
  exact (GrpMor.pull_pull m (homMor (dp0 L) (𝟙 _) f.hom) k (fun _ ↦ rfl) e.symm c).trans
    (GrpMor.pull_pull (homMor (dp0 K) (𝟙 _) f₀.hom) m k (fun _ ↦ rfl) rfl c).symm

theorem exists_isGrpPullback_baseChange {K : Type} (L : Type) [Field K] [Field L] [Algebra K L] {B₀ : AbVar K}
    (f₀ : B₀ ⟶ B₀) : ∃ q : (AbVar.baseChange L B₀).X.left ⟶ B₀.X.left,
      IsGrpPullback (AbVar.baseChange L B₀).X B₀.X (spMap (algebraMap K L)) q ∧
      q ≫ f₀.hom.left = (AbVar.bcMap L f₀).hom.left ≫ q :=
  ⟨pullback.fst B₀.X.hom (spMap (algebraMap K L)), isGrpPullback_pullback B₀.X _, (pullback.lift_fst _ _ _).symm⟩

theorem charpoly_of_pullback {K L : Type} [Field K] [Field L] [Algebra K L] (B₀ : AbVar K) (B : AbVar L)
    {φ : B.X.left ⟶ B₀.X.left} (h : IsGrpPullback B.X B₀.X (spMap (algebraMap K L)) φ) (f₀ : B₀ ⟶ B₀) (f : B ⟶ B)
    (e : φ ≫ f₀.hom.left = f.hom.left ≫ φ) :
    AbVar.charpoly (End.of f) = AbVar.charpoly (End.of f₀) := by
  obtain ⟨q, h', hq⟩ := exists_isGrpPullback_baseChange L f₀
  obtain ⟨i, hi, hφ⟩ := grpPullback_iso h h'
  let u : B ⟶ AbVar.baseChange L B₀ := AbVar.Hom.mk i.hom
  have hu : AbVar.IsIsogeny u := by
    have : IsIso i.hom.left := ⟨⟨i.inv.left, by rw [← Over.comp_left, i.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, i.inv_hom_id, Over.id_left]⟩⟩
    exact ⟨inferInstanceAs (IsFinite i.hom.left), inferInstanceAs (Surjective i.hom.left)⟩
  rw [← AbVar.charpoly_bcMap K L B₀ (End.of f₀)]
  refine AbVar.charpoly_eq_of_isogeny_intertwines L B _ u (End.of f) _ hu (Subtype.ext ?_)
  change f.hom ≫ i.hom = i.hom ≫ (AbVar.bcMap L f₀).hom
  apply Over.OverMorphism.ext
  apply h'.1.hom_ext
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, ← e, ← hq, ← Category.assoc, hφ]
  · rw [Over.w, Over.w]

theorem charpoly_push_complex (B : AbVar ℂ) (f : B ⟶ B) [Module.Finite ℂ (HdR B.X)] :
    LinearMap.charpoly (push (dp0 ℂ) (𝟙 _) f.hom) =
      (AbVar.charpoly (End.of f)).map (Int.castRingHom ℂ) := by
  obtain ⟨L, hL, ⟨u⟩⟩ : ∃ L : LB B.X.left, L.IsLB ∧ Nonempty (HolUnif B.X L B.dim) := by
    have := B.ab.proper
    obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ B.X B.ab
    have hamp : Out.RelAmple B.X H :=
      (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B.X hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
    exact ⟨_, Out.Inh.trivLB_isLB _, GlobalTheory.RealMultChart.exists_holUnif_of_compact B.X B.dim B.smooth
      (GlobalTheory.RealMultChart.compactSpace_points B.X H hamp)
      (fun a n hn => GlobalTheory.RealMultChart.exists_pow_eq B.X B.ab a n hn)⟩
  have ht := GlobalTheory.TorusTransfer.tangent_bijective u B.smooth
  obtain ⟨M, hM, hΛ, -, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom B.X B.X B.ab B.ab L L B.dim B.dim u u
    ht.1 ht.2 f.hom inferInstance
  obtain ⟨ε, hP⟩ := GlobalTheory.PeriodFamily.periodComparison_holds
  obtain ⟨P, hsp, hrk, -, hnat, -⟩ := hP B.X B.dim B.ab B.smooth L hL u
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have hr : Module.finrank ℤ u.Λ = 2 * B.dim := by
    rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  let φ : u.Λ →ₗ[ℤ] u.Λ := (M.restrictScalars ℤ).restrict hΛ
  let E : ℂ ⊗[ℤ] u.Λ →ₗ[ℂ] HdR B.X := P.toIntLinearMap.liftBaseChange ℂ
  have hE1 : ∀ x, E (1 ⊗ₜ x) = P x := fun x => one_smul ℂ (P x)
  have hs : Function.Surjective E := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hE1 x⟩
  have hE : Function.Bijective E :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_baseChange, hr, hrk])).2 hs, hs⟩
  have h1 := charpoly_of_bijective E hE φ (push (dp0 ℂ) (𝟙 _) f.hom) fun x => by
    rw [hE1, hE1]
    exact hnat f.hom M hM x (φ x) rfl
  have hpow : ∀ (n : ℕ) (z : Fin B.dim → ℂ), u.ex (n • z) = u.ex z ^ n := fun n z => by
    induction n with
    | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
    | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]
  have hc : ∀ (j : ℕ) (z : Fin B.dim → ℂ), (2 ^ j : ℕ) • (((2 : ℂ) ^ j)⁻¹ • z) = z := fun j z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    simp
  have hc' : ∀ (j : ℕ) (z : Fin B.dim → ℂ), ((2 : ℂ) ^ j)⁻¹ • ((2 ^ j : ℕ) • z) = z := fun j z => by
    rw [smul_comm, hc]
  have h2 := AbVar.charpoly_eq_lattice_model ℂ B f u.Λ φ 2 Nat.prime_two (by norm_num)
    (fun j x => u.ex (((2 : ℂ) ^ j)⁻¹ • (x : Fin B.dim → ℂ)))
    (fun j x y => by
      simp only [Submodule.coe_add, smul_add]
      exact u.ex_add _ _)
    (fun j x => by
      refine Eq.trans ?_ (hM _)
      rw [map_smul]
      rfl)
    (fun j x => by
      refine (u.ker _).trans ⟨fun h => ⟨⟨_, h⟩, Subtype.ext (hc j x).symm⟩, ?_⟩
      rintro ⟨y, rfl⟩
      rw [show ((2 ^ j • y : u.Λ) : Fin B.dim → ℂ) = (2 ^ j : ℕ) • (y : Fin B.dim → ℂ) from rfl, hc']
      exact y.2)
    (fun j q => by
      obtain ⟨z, rfl⟩ := u.ex_onto q
      constructor
      · intro h
        exact ⟨⟨_, (u.ker _).1 ((hpow _ z).trans h)⟩, congrArg u.ex (hc' j z)⟩
      · rintro ⟨x, hx⟩
        have hx' : u.ex (((2 : ℂ) ^ j)⁻¹ • (x : Fin B.dim → ℂ)) = u.ex z := hx
        change u.ex z ^ (2 ^ j) = 1
        rw [← hx', ← hpow, hc]
        exact (u.ker _).2 x.2)
  rw [h1, h2]
  rfl

theorem exists_countable_model (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (B : AbVar k) (f : B ⟶ B) :
    ∃ (K : Type) (_ : Field K) (_ : Countable K) (_ : Algebra K k) (B₀ : AbVar K) (f₀ : B₀ ⟶ B₀)
      (φ : B.X.left ⟶ B₀.X.left), IsGrpPullback B.X B₀.X (spMap (algebraMap K k)) φ ∧
      φ ≫ f₀.hom.left = f.hom.left ≫ φ := by
  obtain ⟨S, A, _, ψ, -, hS, hA, hg, hψ⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring k B.dim B.X ∅ B.ab B.smooth
  have hSc : Countable S := by
    obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hS
    have hc : Countable (MvPolynomial (Fin n) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      refine (MvPolynomial.cardinalMk_le_max).trans ?_
      simp
    exact hp.countable
  let F : Subfield k := Subfield.closure (S : Set k)
  have hF : Cardinal.mk F ≤ Cardinal.aleph0 :=
    (Subfield.cardinalMk_closure_le_max _).trans (max_le (Cardinal.mk_le_aleph0_iff.2 hSc) le_rfl)
  let K : IntermediateField F k := algebraicClosure F k
  haveI : IsAlgClosed K := (algebraicClosure.isAlgClosure F k).isAlgClosed
  haveI : Module.IsTorsionFree F K := DivisionSemiring.to_moduleIsTorsionFree
  have hK : Countable K := Cardinal.mk_le_aleph0_iff.1
    ((Algebra.IsAlgebraic.cardinalMk_le_max F K).trans (max_le hF le_rfl))
  let j : S →+* K := S.subtype.codRestrict K fun x => K.algebraMap_mem (⟨x, Subfield.subset_closure x.2⟩ : F)
  have e : spMap (algebraMap K k) ≫ spMap j = spMap S.subtype := by
    rw [← Cris.spMap_comp]
    rfl
  let B₀ : AbVar K :=
    { X := (Over.pullback (spMap j)).obj A
      ab := GlobalTheory.isAbelianScheme_pullback_obj _ A hA
      dim := B.dim
      smooth := (smoothOfRelativeDimension_isStableUnderBaseChange (n := B.dim)).of_isPullback
        (IsPullback.of_hasPullback A.hom (spMap j)) hg }
  obtain ⟨φ, hφ⟩ : ∃ φ : B.X.left ⟶ B₀.X.left, IsGrpPullback B.X B₀.X (spMap (algebraMap K k)) φ :=
    ⟨_, Chart.isGrpPullback_factor (spMap j) (spMap (algebraMap K k)) (hψ.congr e.symm rfl)⟩
  obtain ⟨f₀, hf₀, he⟩ := GlobalTheory.AlgClosedHomDescent.hom_descends K k (algebraMap K k) B₀.X B₀.X B.X B.X φ φ
    B₀.ab B₀.ab hφ hφ f.hom inferInstance
  exact ⟨K, inferInstance, hK, inferInstance, B₀, AbVar.Hom.mk f₀, φ, hφ, he⟩

theorem charpoly_push : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
      (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
  intro k _ _ _ B f _
  obtain ⟨K, _, _, _, B₀, f₀, φ, hφ, he⟩ := exists_countable_model k B f
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap K k).injective).2 inferInstance
  obtain ⟨σ⟩ := GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex K
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := finite_HdR B₀
  haveI := finite_HdR (AbVar.baseChange ℂ B₀)
  obtain ⟨q, hq, hq'⟩ := exists_isGrpPullback_baseChange ℂ f₀
  have h3 := charpoly_push_of_pullback B₀ _ hq f₀ _ hq'
  have h4 := charpoly_push_complex (AbVar.baseChange ℂ B₀) (AbVar.bcMap ℂ f₀)
  rw [AbVar.charpoly_bcMap] at h4
  have h5 : LinearMap.charpoly (push (dp0 K) (𝟙 _) f₀.hom) =
      (AbVar.charpoly (End.of f₀)).map (Int.castRingHom K) := by
    apply Polynomial.map_injective (algebraMap K ℂ) σ.injective
    rw [← h3, h4, Polynomial.map_map]
    exact congrArg (Polynomial.map · _) (RingHom.ext_int _ _)
  rw [charpoly_push_of_pullback B₀ B hφ f₀ f he, h5, charpoly_of_pullback B₀ B hφ f₀ f he, Polynomial.map_map]
  exact congrArg (Polynomial.map · _) (RingHom.ext_int _ _)

end GlobalTheory.DeRhamCharpolyZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRham
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CrysFree

theorem isLocalRing_of_sq {Λ k : Type} [CommRing Λ] [Field k] (π : Λ →+* k) (hπ : Function.Surjective π)
    (hI : RingHom.ker π ^ 2 = 0) : IsLocalRing Λ := by
  have hmax : (RingHom.ker π).IsMaximal := RingHom.ker_isMaximal_of_surjective π hπ
  haveI := hmax.isPrime
  have hle : RingHom.ker π ≤ nilradical Λ := fun x hx ↦ ⟨2, by
    have : x * x ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hx
    rw [hI] at this; simpa [pow_two] using this⟩
  have heq : nilradical Λ = RingHom.ker π := le_antisymm (nilradical_le_prime _) hle
  haveI : (nilradical Λ).IsMaximal := heq ▸ hmax
  exact IsLocalRing.of_isMaximal_nilradical Λ

theorem isDPMorphism_red {Λ k : Type} [CommRing Λ] [Field k] (π : Λ →+* k)
    (hI : RingHom.ker π ^ 2 = 0) : DividedPowers.IsDPMorphism (divided₂ hI) (dp0 k) π := by
  refine (DividedPowers.isDPMorphism_iff _ _ _).2 ⟨?_, fun n hn a ha ↦ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]; intro x hx
    simpa using (RingHom.mem_ker.1 hx)
  · rw [RingHom.mem_ker.1 ha]
    rcases n with _ | _ | n
    · exact absurd rfl hn
    · rw [zero_add, (divided₂ hI).dpow_one ha, RingHom.mem_ker.1 ha, (dp0 k).dpow_one (Ideal.zero_mem _)]
    · rw [squareZeroDividedPowers_dpow hI (by omega), map_zero, DividedPowers.dpow_eval_zero _ hn]

theorem mem_smul_top_of_forall {Λ : Type} [CommRing Λ] {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module.Finite Λ P] [Module.Free Λ P] (J : Ideal Λ) (h : Module.Dual Λ P) (hh : ∀ c, h c ∈ J) :
    h ∈ J • (⊤ : Submodule Λ (Module.Dual Λ P)) := by
  classical
  let b := Module.Free.chooseBasis Λ P
  rw [← b.sum_dual_apply_smul_coord h]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hh _) Submodule.mem_top

end GlobalTheory.CrysFree

namespace GlobalTheory.CrysFree

theorem crys_free_and_red : ∀ (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (hπ : Function.Surjective π) (hI : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (divided₂ hI) (spMap π) a; letI := tensorModule (dp0 k) (𝟙 _) a; Module.Finite Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ Module.Free Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ ∃ f : Crys (divided₂ hI) (spMap π) A₀ →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] HdR A₀, Function.Surjective f ∧ ∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ (Crys (divided₂ hI) (spMap π) A₀)) := by
  intro F _ _ Λ _ k _ π hπ hI A₀ _ _ hA₀ a
  haveI := isLocalRing_of_sq π hπ hI
  letI : Algebra Λ k := π.toAlgebra
  obtain ⟨A, _, i, h, hA⟩ := _root_.GlobalTheory.UnobTop.abelianUnobstructed Λ (RingHom.ker π) hI k π hπ rfl A₀ hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim Λ A hA
  obtain ⟨HFree, -, HBC, HRigid, -⟩ := _root_.GlobalTheory.abelianDeRham
  have hrig := HRigid Λ A g hA hg (RingHom.ker π) (divided₂ hI) (isDPNilpotent_squareZero hI) k π hπ rfl A₀ i h
  let e : primDR A ≃ₗ[Λ] prim (divided₂ hI) (spMap π) A₀ :=
    LinearEquiv.ofBijective (liftMor (divided₂ hI) h).pull hrig
  obtain ⟨hfin, hproj, -⟩ := HFree.prim hA hg
  haveI : Module.Finite Λ (prim (divided₂ hI) (spMap π) A₀) := Module.Finite.equiv e
  haveI : Module.Projective Λ (prim (divided₂ hI) (spMap π) A₀) := Module.Projective.of_equiv e
  haveI := Module.finitePresentation_of_projective Λ (prim (divided₂ hI) (spMap π) A₀)
  haveI : Module.Free Λ (prim (divided₂ hI) (spMap π) A₀) := Module.free_of_flat_of_isLocalRing
  have m : GrpMor (divided₂ hI) (spMap π) A₀ (dp0 k) (𝟙 _) A₀ (algebraMap Λ k) (𝟙 _) (Over.Hom.left (𝟙 A₀)) :=
    ⟨isDPMorphism_red π hI, by simp, by simp, by
      intro T x y x₀ y₀ hx hy
      have ex : x₀.left = x.left := by simpa using hx
      have ey : y₀.left = y.left := by simpa using hy
      have eqx : x₀ = x := Over.OverMorphism.ext ex
      have eqy : y₀ = y := Over.OverMorphism.ext ey
      subst x₀
      subst y₀
      simp only [Over.id_left, Category.comp_id]
      rfl⟩
  have hm : m.IsBC := by
    have hb := (HBC Λ A g hA hg k A₀ i h).1
    let E := LinearEquiv.baseChange Λ k _ _ e
    have key : liftSemi m.pull ∘ₗ E.toLinearMap =
        liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h).pull := by
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.baseChange_tmul,
          liftSemi_tmul]
        congr 1
        exact GrpMor.pull_pull (liftMor (divided₂ hI) h) m (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h)
          (fun _ ↦ rfl) (by simp) c
      | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]
    have : liftSemi m.pull = liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h).pull ∘ₗ
        E.symm.toLinearMap := by
      rw [← key, LinearMap.comp_assoc, ← LinearEquiv.coe_trans, LinearEquiv.symm_trans_self]; rfl
    unfold GrpMor.IsBC
    rw [this]
    exact hb.comp E.symm.bijective
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hact : ∀ (o : 𝓞 F) (x : Crys (divided₂ hI) (spMap π) A₀),
      hm.bcMap (act (divided₂ hI) (spMap π) a o x) = act (dp0 k) (𝟙 _) a o (hm.bcMap x) := by
    intro o x
    haveI := a.hom o
    rw [act_apply, act_apply]
    exact hm.corr_iff.1 (GrpMor.Corr.push (m := m) m (a.act o) (a.act o) (by simp) (hm.corr_iff.2 rfl))
  letI := tensorModule (divided₂ hI) (spMap π) a
  letI := tensorModule (dp0 k) (𝟙 _) a
  refine ⟨{ toFun := hm.bcMap, map_add' := hm.bcMap.map_add, map_smul' := ?_ }, ?_, ?_⟩
  · intro r x
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul l o =>
      have e1 : (l ⊗ₜ[ℤ] o) • x = l • act (divided₂ hI) (spMap π) a o x := rfl
      have e2 : ∀ y : HdR A₀, ((Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom
          (l ⊗ₜ[ℤ] o)) • y = π l • act (dp0 k) (𝟙 _) a o y := fun y ↦ rfl
      rw [e1, e2, hm.bcMap.map_smulₛₗ, hact]
      rfl
    | add r s hr hs =>
      rw [add_smul, map_add (f := hm.bcMap), hr, hs, map_add (f := _), add_smul]
  · intro h'
    let l : prim (divided₂ hI) (spMap π) A₀ →ₗ[Λ] k :=
      { toFun c := h' (m.pull c)
        map_add' c d := by rw [map_add (f := _), map_add (f := _)]
        map_smul' r c := by
          rw [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
    obtain ⟨hh, hhl⟩ := Module.projective_lifting_property (Algebra.linearMap Λ k) l hπ
    exact ⟨hh, hm.corr_iff.1 fun c ↦ (LinearMap.congr_fun hhl c).symm⟩
  · intro x hx
    have hc : m.Corr x 0 := hm.corr_iff.2 hx
    exact mem_smul_top_of_forall _ x fun c ↦ RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))

end GlobalTheory.CrysFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfIdempotentFactorBiex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_finExt_evenCP_of_factor_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ ∧ IsGrpPullback G₉ G (spMap ρ₉) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P₉ ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hOL G _ _ hG inc pr hinc hpr hip hpi R₁ _ _ _ ρ₁ G₁ _ _ β₁ β₁₂ A₁ gen₁ hρ₁ hβ₁ hsq₁ hgen₁ hE
  obtain ⟨R₂, _, _, _, ρ₂, D₂, D₂', F₂, A₂', G₂', _, _, U₂', oA₂, oG₂, G₂, _, _, inc₂, pr₂, β₂, β₂₂, A₂, gen₂, W, _, _, _,
    φ, GW, _, _, βW, DW, AW, UW, κ, hρ₂, hR₂, hG₂', hOL₂, hG₂, hinc₂, hpr₂, hip₂, hpi₂, hβ₂, hsq₂, hgen₂, hE₂, hPP₂,
    hW, hφ, hφl, hβW, hκ, hUW⟩ :=
    _root_.GlobalTheory.Mum.FactorMove.exists_finExt_factor_trait R hR D D' F A' G' hG' U' oA oG hOL G hG inc pr hinc hpr hip hpi R₁ ρ₁ G₁ β₁ β₁₂ A₁ gen₁ hρ₁ hβ₁ hsq₁ hgen₁ hE
  obtain ⟨R₃, _, _, _, ρ₃, G₃, _, _, β₃, κ₃, L₃, hρ₃, hβ₃, hκ₃, hL₃, hL₃iso⟩ :=
    _root_.GlobalTheory.Mum.exists_finExt_lbExt_of_factor R₂ hR₂ D₂ D₂' F₂ A₂' G₂' hG₂' U₂' oA₂ oG₂ hOL₂ G₂ hG₂ inc₂ pr₂ hinc₂ hpr₂ hip₂ hpi₂ A₂ gen₂ hgen₂ hE₂
      W hW φ hφ hφl GW βW DW AW UW κ hβW hκ hUW
  obtain ⟨R₉, _, _, _, ρ, G₉, _, _, β₉, β₉₂, P, A₉, gen₉, hρ, hβ₉, hsq₉, hG₉, hlam, hev, hgen₉, hiso₉⟩ :=
    _root_.GlobalTheory.Mum.exists_even_package_of_ext R₂ hR₂ G₂ hG₂ A₂ gen₂ hgen₂ _ hE₂ W φ GW βW DW AW UW κ hW hφ hφl hβW hκ hUW R₃ ρ₃ G₃ β₃ κ₃ L₃ hρ₃ hβ₃ hκ₃
      hL₃ hL₃iso
  have hΛ : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb U'.LG.isLB _ _
  have hΛ₂ : (abelian₂ G₂' U₂'.LG.L).IsLB := LB.isLB_linComb U₂'.LG.isLB _ _
  refine ⟨R₉, inferInstance, inferInstance, inferInstance, ρ.comp ρ₂, G₉, inferInstance, inferInstance, β₉ ≫ β₂,
    β₉₂ ≫ β₂₂, P, A₉, gen₉, ⟨hρ.1, hρ.2.1.comp hρ₂.2.1, hρ.2.2.comp hρ₂.2.2⟩, ?_, ?_, hG₉, ?_, hev, hgen₉, hiso₉⟩
  · rw [spMap_comp]
    exact hβ₉.comp hβ₂
  · exact ⟨by rw [Category.assoc, hsq₂.1, ← Category.assoc, hsq₉.1, Category.assoc],
      by rw [Category.assoc, hsq₂.2, ← Category.assoc, hsq₉.2, Category.assoc]⟩
  · have a := GlobalTheory.GenSpread.lbIso_pullback hPP₂ β₉₂
    have b := GlobalTheory.GenSpread.lbIso_pull_pull (pull_isLB hΛ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) β₉₂ (a' := β₉₂ ≫ β₂₂) rfl
    have c := GlobalTheory.GenSpread.lbIso_pull_pull hΛ (β₉₂ ≫ β₂₂)
      (a' := (β₉₂ ≫ β₂₂) ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) rfl
    have hL : (abelian₂ G₉ P.L.L).IsLB := LB.isLB_linComb P.L.isLB _ _
    refine LBIso.trans hL (pull_isLB (pull_isLB hΛ₂ _) _) (pull_isLB hΛ _) hlam ?_
    refine LBIso.trans (pull_isLB (pull_isLB hΛ₂ _) _) (pull_isLB (pull_isLB (pull_isLB hΛ _) _) _) (pull_isLB hΛ _) a ?_
    refine LBIso.trans (pull_isLB (pull_isLB (pull_isLB hΛ _) _) _) (pull_isLB (pull_isLB hΛ _) _) (pull_isLB hΛ _)
      (LBIso.symm b) (LBIso.symm c)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCrystalActionAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem crysAct_adjoint : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (c : D.O) x y, φ (GlobalTheory.HTCount.crysAct o₀ c x) y = φ x (GlobalTheory.HTCount.crysAct o₀ (D.star c).unop y) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ hφ c x y
  haveI := o₀.act.hom c
  haveI := o₀.act.hom (D.star c).unop
  have hA := o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k o₀.A hA
  have C := GlobalTheory.AbDual.cupSquare_of_free GlobalTheory.abelianDeRham.1
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA) (GlobalTheory.AbDual.smooth_prod hg hg)
  have e := GlobalTheory.AbDual.IsCorrForm.adjoint C o₀.isLB o₀.isLB hφ hφ (o₀.act.act c) (o₀.act.act (D.star c).unop)
    (LBIso.symm (o₀.rosati c)) x y
  rw [GlobalTheory.HTCount.crysAct_apply, GlobalTheory.HTCount.crysAct_apply]
  exact e.symm

end GlobalTheory.HTCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsSymbolZeroTorsionPointsHorizontalStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperators_symbol_zero_torsion_points_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ y : P.D.toPre.X, ∃ c' : Sp (DualNumber k) ⟶ B'.left, c' ≫ B'.hom = 𝟙 _ ∧ c' ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  first | exact @GlobalTheory.HeatPts.exists_horizontal_section | exact GlobalTheory.HeatPts.exists_horizontal_section | (intros; apply GlobalTheory.HeatPts.exists_horizontal_section <;> assumption)
end

