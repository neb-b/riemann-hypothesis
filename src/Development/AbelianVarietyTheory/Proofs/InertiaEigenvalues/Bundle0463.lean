module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlWcbInjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Formalism.LocalRingCardinality.HostCls
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0073
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0431
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulCocycle
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.HerrExtUnit

theorem exists_unit (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    let S := sit D.loc HW l (D.locA l) K s LL h
    let E : S.Comparison₂ := ((F l).E K s LL h).tie
    ∀ (e : S.W.DD S.W.one) (t : ↥S.W.one.L.T),
      S.W.N S.W.one = Submodule.span (LetA S.O S.n) {e} → S.W.φD S.W.one e = e →
      Submodule.span S.O {(t : S.W.one.V)} = S.W.one.L.T →
      ∃ u : (S.O)ˣ, ∀ a : S.O,
        E.jD S.W.one (a • e) = (1 : S.RW) ⊗ₜ[S.O] (((u : S.O) * a) • t) := by
  intro S E e t hN hφ ht
  obtain ⟨u, hu'⟩ : ∃ u : (S.O)ˣ, E.jD S.W.one e = (algebraMap S.O S.RW (u : S.O)) ⊗ₜ[S.O] t :=
    GlobalTheory.Cyc.UnitGen.main D HW F l K s LL h e t hN hφ ht
  refine ⟨u, fun a => ?_⟩
  rw [map_smul, hu', Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_smul, smul_smul, mul_comm]

theorem smul_cocycle (S : Sit) {T Tp : LocLat S.G S.Qp S.LL S.O} (ι : LatHom T.L Tp.L) (x : T.V)
    (g : S.G) (et : Tp.V) (hx : ι.f x = Tp.ρ g et - et) (b : S.O) :
    ι.f (b • x) = Tp.ρ g (b • et) - b • et := by
  rw [← algebraMap_smul S.LL b x, ← algebraMap_smul S.LL b et, map_smul, map_smul, hx, smul_sub]

theorem smul_proj (S : Sit) {Tp Z : LocLat S.G S.Qp S.LL S.O} (π : LatHom Tp.L Z.L)
    (et : Tp.V) (b : S.O) : b • π.f et = π.f (b • et) := by
  rw [← algebraMap_smul S.LL b et, map_smul, algebraMap_smul]

theorem over_Ks (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    Formalism.MainNotions.ElementDenominator.coreHerrExt (sit D.loc HW l (D.locA l) K s LL h).W := by
  intro T Tp ι π _ _ c hc hE e he
  obtain ⟨hS, et, het, hgen, hcoc⟩ := hE
  obtain ⟨u, hu⟩ := exists_unit D HW F l K s LL h e ⟨π.f et, π.T_le _ het⟩ he.1 he.2.1 hgen
  refine ⟨u, fun x a hx y z hyz h1 h2 => ?_⟩
  have key := GlobalTheory.Cyc.dict_ext_Ks D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    T Tp _ ι π hS (sit D.loc HW l (D.locA l) K s LL h).W.one_triv
    ((u.1 * a) • ⟨et, het⟩) ((u.1 * a) • ⟨π.f et, π.T_le _ het⟩) x
    (smul_proj _ π et _) (by rw [hx]; exact hu a) ⟨(y, z), hyz⟩ h1 h2
    ((u.1 * a) • ⟨_, resFun_Z1T T _ c hc⟩)
    (fun g => smul_cocycle _ ι _ g et (hcoc g) _)
  exact key.trans (Submodule.Quotient.mk_smul _ _ _)

theorem over_K (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    Formalism.MainNotions.ElementDenominator.coreHerrExtΔ (sit D.loc HW l (D.locA l) K s LL h).W := by
  intro _ hp T Tp ι π _ _ c hc hE e he
  obtain ⟨hS, et, het, hgen, hcoc⟩ := hE
  obtain ⟨u, hu⟩ := exists_unit D HW F l K s LL h e ⟨π.f et, π.T_le _ het⟩ he.1 he.2.1 hgen
  refine ⟨u, fun x a hδ hx y z hyz h1 h2 => ?_⟩
  have key := GlobalTheory.ExtDict.dict_K D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    (fun h2 => absurd h2 hp) T Tp _ ι π hS (sit D.loc HW l (D.locA l) K s LL h).W.one_triv
    ((u.1 * a) • ⟨et, het⟩) ((u.1 * a) • ⟨π.f et, π.T_le _ het⟩) x
    (smul_proj _ π et _) (by rw [hx]; exact hu a) hδ ⟨(y, z), hyz⟩ h1 h2
    ((u.1 * a) • ⟨c, hc⟩)
    (fun g => smul_cocycle _ ι _ g et (hcoc g) _)
  exact key.trans (Submodule.Quotient.mk_smul _ _ _)

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.HerrComplexNaturality.HerrExtensionUpToUnit D HW F :=
  fun D HW F l _ K s LL h => ⟨over_Ks D HW F l K s LL h, over_K D HW F l K s LL h⟩

end GlobalTheory.HerrExtUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiFil

variable {l : ℕ} [Fact l.Prime]

theorem mem_FilD_zero_iff (x : Per.BdR l) :
    x ∈ Per.FilD l 0 ↔ ∃ z : Per.BdRp l, x = algebraMap (Per.BdRp l) (Per.BdR l) z := by
  have h := GlobalTheory.BdRQuot.mem_FilD_nat (l := l) 0 x
  rw [Nat.cast_zero] at h
  rw [h]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, GlobalTheory.BdRQuot.mem_filtration_zero z, rfl⟩

theorem mul_mem_FilD_of_zero {x y : Per.BdR l} {n : ℤ} (hx : x ∈ Per.FilD l 0) (hy : y ∈ Per.FilD l n) :
    x * y ∈ Per.FilD l n := by
  obtain ⟨z, rfl⟩ := (mem_FilD_zero_iff x).1 hx
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ z hy

theorem mul_mem_FilD_neg {x y : Per.BdR l} {m : ℕ} (hx : x ∈ Per.FilD l m) (hy : y ∈ Per.FilD l (-(m : ℤ))) :
    x * y ∈ Per.FilD l 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.BdRField.exists_isEps l
  obtain ⟨w, rfl⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he _ x).1 hx
  obtain ⟨w', rfl⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he _ y).1 hy
  rw [mul_mul_mul_comm, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_mul,
    ← map_mul]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def filO (C : GlobalTheory.MemLoc.Core l) (n : ℤ) : Submodule O (OB l O) :=
  Submodule.span O {x | ∃ β : Per.Bcris l, C.ι β ∈ Per.FilD l n ∧ x = (1 : O) ⊗ₜ[ℤ_[l]] β}

variable {O} {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

def filT (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) (n : ℤ) : Submodule O (TW (OB l O) T) :=
  Submodule.span O {w | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l n ∧
    w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}

theorem smul_mem_filT {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {a b c : ℤ}
    (hmul : ∀ β β' : Per.Bcris l, C.ι β ∈ Per.FilD l a → C.ι β' ∈ Per.FilD l b → C.ι (β * β') ∈ Per.FilD l c)
    {r : OB l O} (hr : r ∈ filO O C a) {v : TW (OB l O) T} (hv : v ∈ filT C T b) : r • v ∈ filT C T c := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨β, hβ, rfl⟩ := hr
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨β', x, hβ', rfl⟩ := hv
      rw [smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      exact Submodule.subset_span ⟨β * β', x, hmul β β' hβ hβ', rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add v v' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | smul o v _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h
  | zero => rw [zero_smul]; exact zero_mem _
  | add r r' _ _ h h' => rw [add_smul]; exact add_mem h h'
  | smul o r _ h => rw [smul_assoc]; exact Submodule.smul_mem _ o h

theorem smul_mem_filT_of_zero {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {n : ℤ} {r : OB l O}
    (hr : r ∈ filO O C 0) {v : TW (OB l O) T} (hv : v ∈ filT C T n) : r • v ∈ filT C T n :=
  smul_mem_filT (fun β β' h h' => by rw [map_mul]; exact mul_mem_FilD_of_zero h h') hr hv

theorem smul_mem_filT_neg {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {m : ℕ} {r : OB l O}
    (hr : r ∈ filO O C m) {v : TW (OB l O) T} (hv : v ∈ filT C T (-(m : ℤ))) : r • v ∈ filT C T 0 :=
  smul_mem_filT (fun β β' h h' => by rw [map_mul]; exact mul_mem_FilD_neg h h') hr hv

end GlobalTheory.BKGal.XiFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.BurnsideField

open scoped MonoidAlgebra

theorem span_range_eq_top_of_isAlgClosed {G K V : Type} [Group G] [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V)
    (h : τ.IsIrreducible) : Submodule.span K (Set.range τ) = ⊤ := by
  classical
  have hscal : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := K[G]) (V := τ.asModule) K).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  have hsurj : Function.Surjective τ.asAlgebraHom := by
    intro f
    let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
      { toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m))
        map_add' := fun x y => by simp
        map_smul' := fun φ m => by
          obtain ⟨c, hc⟩ := hscal φ
          simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F
      (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))
    refine ⟨r, b.ext fun i => ?_⟩
    have := congrArg τ.asModuleEquiv (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    exact this.symm
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨r, rfl⟩ := hsurj f
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | single g c =>
    rw [Representation.asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

theorem span_mat_eq_top_of_isIrrSub {Γ K : Type} [Group Γ] [Field K] [IsAlgClosed K] {r : ℕ}
    (σ : Γ →* GL (Fin r) K) (h : IsIrrSub σ ⊤) : Submodule.span K (Set.range (mat σ)) = ⊤ := by
  classical
  let τ : Representation K Γ (Fin r → K) :=
    { toFun := fun g => Matrix.toLin' (mat σ g)
      map_one' := by simp [mat]; rfl
      map_mul' := fun g g' => by simp [mat, Matrix.toLin'_mul]; rfl }
  have hτ : ∀ g v, τ g v = (mat σ g).mulVec v := fun g v => Matrix.toLin'_apply _ _
  have hirr : τ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation τ) := by
      refine ⟨⊥, ⊤, fun hbt => h.1 ?_⟩
      exact (congrArg Subrepresentation.toSubmodule hbt).symm
    refine ⟨fun W => ?_⟩
    rcases h.2.2 W.toSubmodule le_top (fun g v hv => by
      have := W.apply_mem_toSubmodule g hv
      rwa [hτ] at this) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  have hs := span_range_eq_top_of_isAlgClosed τ hirr
  have hm : Set.range (mat σ) = (LinearMap.toMatrix' (R := K) (m := Fin r) (n := Fin r)) '' Set.range τ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (LinearMap.toMatrix'_toLin' (mat σ g)).symm
  rw [hm]
  have := Submodule.map_span (LinearMap.toMatrix' (R := K) (m := Fin r) (n := Fin r)).toLinearMap
    (Set.range τ)
  rw [hs, Submodule.map_top, LinearEquiv.range] at this
  exact this.symm

theorem span_eq_top_of_span_map {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k)
    (h : Submodule.span K (Set.range fun g => (M g).map (algebraMap k K)) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let F : Matrix (Fin r) (Fin r) K →ₗ[K] K :=
    { toFun := fun X => ∑ i, ∑ j, X i j * algebraMap k K (f (Matrix.single i j 1))
      map_add' := fun X Y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c X => by simp [Finset.mul_sum, mul_assoc] }
  have hF : ∀ X : Matrix (Fin r) (Fin r) k, F (X.map (algebraMap k K)) = algebraMap k K (f X) := by
    intro X
    conv_rhs => rw [Matrix.matrix_eq_sum_single X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    change ∑ i, ∑ j, algebraMap k K (X i j) * algebraMap k K (f (Matrix.single i j 1)) = _
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, map_mul]
  have hker : (⊤ : Submodule K (Matrix (Fin r) (Fin r) K)) ≤ LinearMap.ker F := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    have : f (M g) = 0 := hf (Submodule.subset_span ⟨g, rfl⟩)
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hF, this, map_zero]
  apply hf0
  refine LinearMap.ext fun X => ?_
  have h1 : F (X.map (algebraMap k K)) = 0 := hker trivial
  rw [hF] at h1
  exact (algebraMap k K).injective (by rw [h1]; simp)

theorem span_mat_eq_top_of_absIrrSub :
    ∀ {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (ρ : Γ →* GL (Fin r) k), AbsIrrSub ρ ⊤ → Submodule.span k (Set.range (mat ρ)) = ⊤ := by
  intro Γ k _ _ r ρ h
  classical
  have htop : Submodule.span (AlgebraicClosure k)
      ((fun v : Fin r → k => (algebraMap k (AlgebraicClosure k)) ∘ v) ''
      ((⊤ : Submodule k (Fin r → k)) : Set (Fin r → k))) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (AlgebraicClosure k) (Fin r)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, trivial, ?_⟩
    ext x
    by_cases hx : x = j
    · subst hx; simp
    · simp [hx]
  unfold AbsIrrSub at h
  rw [htop] at h
  have h2 := span_mat_eq_top_of_isIrrSub _ h
  have h3 : mat (mapRep (algebraMap k (AlgebraicClosure k)) ρ) =
      fun g => (mat ρ g).map (algebraMap k (AlgebraicClosure k)) := by
    funext g
    ext p q
    simp [mat, mapRep]
  rw [h3] at h2
  exact span_eq_top_of_span_map (mat ρ) h2

end GlobalTheory.BurnsideField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitPlaces

variable {R : Ranks} (H : Host R)

theorem sqrt_sq : (H.sqd) ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem conj_sqrt : H.conj (H.sqd) = -H.sqd :=
  by apply _root_.UpperTheory.Reformulated.B.Rc9.conj_sqrt <;> assumption

theorem exists_conjPl (l : ℕ) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E l) :
    ∃ w' ∈ placesOver H.E l, IsConjPl H w w' := by
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  refine ⟨HeightOneSpectrum.comap (c.symm : 𝓞 H.E →+* 𝓞 H.E) c.symm.surjective w, ?_, ?_⟩
  · show (c.symm : 𝓞 H.E →+* 𝓞 H.E) (l : 𝓞 H.E) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  · intro x y hxy
    have : y = c x := by
      apply RingOfIntegers.ext
      rw [hxy]; rfl
    subst this
    show _ ↔ c.symm (c x) ∈ w.asIdeal
    rw [c.symm_apply_apply]

theorem not_isConjPl_self {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hld : l ≠ H.d)
    (hj : jacobiSym (-(H.d : ℤ)) l = 1) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E l) :
    ¬ IsConjPl H w w := by
  intro h
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨m, hm⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective m
  have hdvd : (l : ℤ) ∣ n * n + H.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hm ⊢
    rw [← hm]; ring
  have hint : IsIntegral ℤ (H.sqd) := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [sqrt_sq]
    exact (isIntegral_natCast _).neg
  let b : 𝓞 H.E := ⟨H.sqd, hint⟩
  have hb : b ^ 2 = -(H.d : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    have e : ((b : 𝓞 H.E) : H.E) = H.sqd := rfl
    simp only [map_neg, map_pow, map_natCast, e]
    exact sqrt_sq H
  have hiff : b - n ∈ w.asIdeal ↔ b + n ∈ w.asIdeal := by
    rw [h (b - n) (-(b + n)) ?_, neg_mem_iff]
    have e : ((b : 𝓞 H.E) : H.E) = H.sqd := rfl
    simp only [map_neg, map_add (f := _), map_sub, map_intCast, e, conj_sqrt]
    ring
  have hprod : (b - n) * (b + n) ∈ w.asIdeal := by
    obtain ⟨k, hk⟩ := hdvd
    have hk' : ((n * n + H.d : ℤ) : 𝓞 H.E) = ((l * k : ℤ) : 𝓞 H.E) := by rw [hk]
    push_cast at hk'
    have : (b - n) * (b + n) = (l : 𝓞 H.E) * (-k) := by
      linear_combination hb - hk'
    rw [this]
    exact w.asIdeal.mul_mem_right _ hw
  have hboth : b - n ∈ w.asIdeal ∧ b + n ∈ w.asIdeal := by
    rcases w.isPrime.mem_or_mem hprod with h1 | h1
    exacts [⟨h1, hiff.mp h1⟩, ⟨hiff.mpr h1, h1⟩]
  have h2n : ((2 * n : ℤ) : 𝓞 H.E) ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem hboth.2 hboth.1
    convert this using 1
    push_cast; ring
  have hlo := GlobalTheory.HubLoc.liesOver_of_mem hl hw
  have hl2n : (l : ℤ) ∣ 2 * n := by
    rw [← Ideal.mem_span_singleton, hlo.over, Ideal.under_def, Ideal.mem_comap]
    simpa using h2n
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  rcases hp.dvd_or_dvd hl2n with h1 | h1
  · have h3 : l ∣ 2 := by exact_mod_cast h1
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h3)
  · have h3 : (l : ℤ) ∣ H.d := (dvd_add_right (h1.mul_right n)).mp hdvd
    have h4 : l ∣ H.d := by exact_mod_cast h3
    exact hld ((Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).mp h4)

theorem placesSplit : ∀ {R : Ranks} (H : Host R) (l : ℕ), SplitRowPrime H l → PlacesSplit H l := by
  intro R H l ⟨hl, h5, _, hd, _, hc⟩ w hw
  have hl2 : l ≠ 2 := by omega
  obtain ⟨hN, hj⟩ := (primeClass_eq_splitK_iff' (H := H.toHostRaw) hl).1 hc
  refine ⟨GlobalTheory.HubLoc.ramIdx_eq_one H hl hN w hw, exists_conjPl H l w hw, ?_⟩
  rintro w' h rfl
  exact not_isConjPl_self H hl hl2 hd hj _ hw h

end GlobalTheory.SplitPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorOneInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TensorOneInj

theorem bcris_nontrivial (l : ℕ) [Fact l.Prime] : Nontrivial (Per.Bcris l) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  have : Nontrivial (Per.BdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.nontrivial
  exact C.ι.domain_nontrivial

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap ℤ_[l] (Per.Bcris l)) := by
  have := bcris_nontrivial l
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (algebraMap ℤ_[l] (Per.Bcris l) (PadicInt.unitCoeff h0 : ℤ_[l])) :=
    (PadicInt.unitCoeff h0).isUnit.map _
  exact (hu.mul ((GlobalTheory.MemLoc.isUnit_l_Bcris l).pow _)).ne_zero hx

theorem algebraMap_OB_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] : Function.Injective (algebraMap O (OB l O)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ_[l] (Per.Bcris l)) (algebraMap_injective l)
  have e : ⇑(algebraMap O (OB l O)) =
      (LinearMap.lTensor O (Algebra.linearMap ℤ_[l] (Per.Bcris l))) ∘ (TensorProduct.rid ℤ_[l] O).symm := by
    funext o
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [e]
  exact h.comp (TensorProduct.rid ℤ_[l] O).symm.injective

theorem tensor_one_injective : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O),
    Function.Injective fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ O K _ _ _ _ _ _ _ _ G _ _ T
  haveI : Module.Free O ↥T.L.T := T.L.free
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T)
    (Algebra.linearMap O (OB l O)) (algebraMap_OB_injective l O)
  have e : (fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x) =
      (LinearMap.rTensor (↥T.L.T) (Algebra.linearMap O (OB l O))) ∘ (TensorProduct.lid O ↥T.L.T).symm := by
    funext x
    simp [Algebra.TensorProduct.one_def]
  rw [e]
  exact h.comp (TensorProduct.lid O ↥T.L.T).symm.injective

end GlobalTheory.TensorOneInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUniformizerPowEqMulUnitStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_uniformizer_pow_eq_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ϖ : OCb l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∃ x : OCb l, IsUnit x ∧ bk.flat ^ bk.Ep.natDegree = ϖ * x := by
  first | (exact @GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit) | (exact GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit) | (intros; apply GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit  <;> assumption)
end

