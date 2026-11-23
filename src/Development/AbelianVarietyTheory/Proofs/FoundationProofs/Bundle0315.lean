module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCompactKinfAndConj
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp.KinfCompact

section Mat

variable {p q n : ℕ} {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ}
  {G m : Matrix (Fin n) (Fin n) ℂ}

end Mat

variable {D : D7}

theorem isClosed_realPts (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

theorem continuous_realMat {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    Continuous fun h => infMat D.sp.cm.sig V.gram (θ τ) h := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ τ = θ₀ (tauE D τ) := SmoothForms.RealPts.infEmb_unique _ _ _ (hθ τ) (hθ₀ _)
  rw [e]
  exact ((GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1 (tauE D τ)).2.2.2.1

end GlobalTheory.Cusp.KinfCompact

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
section
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}

theorem isParamVec_iff_isSysParam (hJ : SphOff J χ Sb) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ Sb)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = v) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g)
    {c : List ℤ → ℂ} (hc : ∀ d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c d • f) (B : Multiset ℂˣ) :
    IsParamVec D.sp.cm.sig V.gram (frameLat V) h ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) f B ↔
      IsSysParam D.sp.cm.sig V.rank h c B := by
  have hx : f ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
      (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext (hf k hk)
  have hs := isEigenSys_of_heckeLin hJ hv h hx hc
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  exact ⟨hs.isSysParam, hs.isParamVec h0 hx
    (fun hv => (SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hspan h hv hd).imp fun _ he => he.1)
    fun hw τ hτ => ((((exists_isInertChart _ (isCMExt_host D) v).2 w h hw).2.2.2.2 τ hτ).2 _ _ _ hH hL.fg
      hspan hd).imp fun _ he => he.1⟩

theorem isParamFunV_iff_isSysParamD (hJ : SphOff J χ Sb) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ v ∉ Sb, ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g)
    {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    (hc : ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) (B : Fam D.host.E) :
    IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B :=
  forall₂_congr fun v hv => forall₂_congr fun w h => isParamVec_iff_isSysParam hJ hv h h0 (hf v hv) (hc w) (B w)

theorem isParamFunV_iff_isSysParamD_of_level (hJ : SphOff J χ Sb) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    (hc : ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) (B : Fam D.host.E) :
    IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B :=
  isParamFunV_iff_isSysParamD hJ h0 (fun _ hv _ hk => fixed_of_level hJ hv hf hk) hc B

variable {S : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S}

theorem isParamFunV_iff_of_mem_partFull (hJ : SphOff J χ Sb) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    {T : MMap M} (hT : T ∈ partFull θ M J χ Sb c) {x : M.Vec} (h0 : T x ≠ 0) (B : Fam D.host.E) :
    IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank c B :=
  have h := (mem_partFull θ M J χ Sb c T).1 hT
  isParamFunV_iff_isSysParamD_of_level hJ h0 (((GlobalTheory.MultMem.mem_mult_iff ..).1 h.1).lev x)
    (fun P d R hR => h.2 P d R hR x) B

theorem param_iff_sysParam (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (B : Fam D.host.E) (hJ : SphOff J χ Sb) :
    (∀ f : GA D V → ℂ, f ≠ 0 →
      (∀ v ∉ Sb, ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g) →
      (∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) →
      (IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B)) ∧
    ∀ (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S),
      ∀ T ∈ partFull θ M J χ Sb c, ∀ x : M.Vec, T x ≠ 0 →
        (IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank c B) :=
  ⟨fun _ h0 hf hc => isParamFunV_iff_isSysParamD hJ h0 hf hc B,
    fun _ _ _ _ hT _ h0 => isParamFunV_iff_of_mem_partFull hJ hT h0 B⟩

theorem sphOff_KsphC (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    SphOff (KsphC V ∅) (fun _ => 1) Sb := fun P _ => by
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (comp_finAdEquiv D) P
  exact ⟨e, f, h, fun _ _ => Iff.rfl, fun _ _ _ => rfl⟩

end GlobalTheory.LFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemExtSubSpanDepth
section
noncomputable section

namespace GlobalTheory.Cusp.FlagCocompact

open scoped TensorProduct
open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

theorem exists_adapted_set {K M : Type} [Field K] [AddCommGroup M] [Module K M] (X : ℕ → Submodule K M)
    (hX : Monotone X) (h0 : X 0 = ⊥) (k : ℕ) :
    ∃ s : Set M, LinearIndepOn K id s ∧ s ⊆ X k ∧ ∀ i ≤ k, X i ≤ Submodule.span K (s ∩ X i) := by
  induction k with
  | zero => exact ⟨∅, linearIndepOn_empty _ _, Set.empty_subset _, fun i hi => by
      rw [Nat.le_zero.1 hi, h0]; exact bot_le⟩
  | succ k ih =>
    obtain ⟨s, hs, h1, h2⟩ := ih
    have h3 : s ⊆ X (k + 1) := h1.trans (hX k.le_succ)
    refine ⟨hs.extend h3, hs.linearIndepOn_extend h3, hs.extend_subset h3, fun i hi => ?_⟩
    rcases Nat.le_succ_iff.1 hi with h | rfl
    · exact (h2 i h).trans (Submodule.span_mono (Set.inter_subset_inter_left _ (hs.subset_extend h3)))
    · rw [Set.inter_eq_left.2 (hs.extend_subset h3)]
      exact hs.subset_span_extend h3

theorem exists_adapted_basis {K M : Type} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (X : ℕ → Submodule K M) (hX : Monotone X) (h0 : X 0 = ⊥) (k : ℕ) :
    ∃ (r : ℕ) (e : Fin r → M) (d : Fin r → ℕ), LinearIndependent K e ∧ (∀ j, d j < k) ∧
      ∀ i ≤ k, X i = Submodule.span K (e '' {j | d j < i}) := by
  classical
  obtain ⟨s, hs, h1, h2⟩ := exists_adapted_set X hX h0 k
  have hf : Finite s := LinearIndependent.finite (R := K) hs
  obtain ⟨r, ⟨q⟩⟩ := Finite.exists_equiv_fin s
  let e : Fin r → M := fun j => (q.symm j).1
  have he : LinearIndependent K e := LinearIndependent.comp hs q.symm q.symm.injective
  have hex : ∀ j, ∃ i, e j ∈ X (i + 1) := fun j => ⟨k, hX k.le_succ (h1 (q.symm j).2)⟩
  have hd : ∀ j i, Nat.find (hex j) < i ↔ e j ∈ X i := fun j i => by
    refine ⟨fun h => hX (Nat.succ_le_of_lt h) (Nat.find_spec (hex j)), fun h => ?_⟩
    cases i with
    | zero => rw [h0] at h; exact absurd h (he.ne_zero j)
    | succ i => exact Nat.lt_succ_of_le (Nat.find_min' _ h)
  refine ⟨r, e, fun j => Nat.find (hex j), he, fun j => (hd j k).2 (h1 (q.symm j).2), fun i hi => le_antisymm
    ((h2 i hi).trans (Submodule.span_mono ?_)) (Submodule.span_le.2 ?_)⟩
  · rintro x ⟨hx, hx'⟩
    have : e (q ⟨x, hx⟩) = x := by simp [e]
    exact ⟨q ⟨x, hx⟩, (hd _ _).2 (this.symm ▸ hx'), this⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact (hd _ _).1 hj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E}


omit [NumberField F] in
theorem mem_extSub_span_depth {R : Type} [CommRing R] [Algebra F R] {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) E}
    (d : Fin r → ℕ) (i : ℕ) (y : Fin V.rank → R ⊗[F] E) :
    y ∈ extSub (F := F) V R (Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i})) ↔
      ∃ a : Fin r → R ⊗[F] E, (∀ j, i ≤ d j → a j = 0) ∧ y = (C.map (inclR (F := F) R)).mulVec a := by
  let C' : Matrix (Fin V.rank) (Fin r) E := fun a j => if d j < i then C a j else 0
  have e : Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i}) = colSpan V C' := by
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨j, hj, rfl⟩
      exact ⟨j, congrArg (vecOf V) (funext fun a => if_pos hj)⟩
    · rintro _ ⟨j, rfl⟩
      by_cases hj : d j < i
      · exact Submodule.subset_span ⟨j, hj, congrArg (vecOf V) (funext fun a => (if_pos hj).symm)⟩
      · have : C'ᵀ j = 0 := funext fun a => if_neg hj
        simp [this, vecOf]
  rw [e, AutFunCompare.mem_extSub_colSpan]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun j => if d j < i then a j else 0, fun j hj => if_neg (not_lt.2 hj), funext fun b => ?_⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d j < i <;> simp [C', hj]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, funext fun b => ?_⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d j < i
    · simp [C', hj]
    · rw [ha j (not_lt.1 hj), mul_zero, mul_zero]

theorem exists_adapted_frame (𝔉 : IsoFlag V) : ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) E) (d : Fin r → ℕ),
    LinearIndependent E Cᵀ ∧ (∀ j, d j < 𝔉.k) ∧
      ∀ i, 𝔉.X i = Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i.val}) := by
  have : Module.Finite E V.V := Module.Finite.of_basis V.frame
  obtain ⟨r, e, d, he, hd, hX⟩ := exists_adapted_basis (K := E)
    (fun i => 𝔉.X ⟨min i 𝔉.k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
    (fun a b h => 𝔉.strictMono.monotone (Fin.mk_le_mk.2 (min_le_min_right _ h)))
    (by rw [← 𝔉.zero]; congr 1) 𝔉.k
  refine ⟨r, Matrix.of fun a j => V.frame.repr (e j) a, d, he.map' V.frame.equivFun.toLinearMap (LinearEquiv.ker _),
    hd, fun i => ?_⟩
  have e1 : (fun k => vecOf V ((Matrix.of fun a j => V.frame.repr (e j) a)ᵀ k)) = e :=
    funext fun k => V.frame.equivFun.symm_apply_apply (e k)
  rw [e1, ← hX i (Nat.lt_succ_iff.1 i.2)]
  congr 1
  ext
  simp [Nat.lt_succ_iff.1 i.2]

theorem unip_cocompact (hc : CMData F E) (𝔉 : IsoFlag V) : Cocompact (ratPts hc V) (𝔉.unip hc (AF F)) := by
  obtain ⟨r, C, d, hC, hd, hX⟩ := exists_adapted_frame 𝔉
  have ht : 𝔉.top = colSpan V C := (hX _).trans (congrArg (Submodule.span _) (by
    rw [← Set.image_univ]; congr 1; exact Set.eq_univ_of_forall fun j => hd j))
  have h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0 := by
    have h := 𝔉.iso
    change 𝔉.top ≤ perp V 𝔉.top at h
    rw [ht] at h
    ext a k
    have := (mem_perp_colSpan hc V C _).1 (h (Submodule.subset_span ⟨k, rfl⟩))
    simp only [repr_vecOf] at this
    exact congrFun this a
  have hm : ∀ (g : GA hc V) (x : Fin V.rank → E),
      ((HA.mat _ hc.sig V.gram g).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
      act hc V g (coordR V _ (vecOf V x)) - coordR V _ (vecOf V x) := fun g x => by
    have : coordR (F := F) V (AF F) (vecOf V x) = fun i => inclR (F := F) (AF F) (x i) :=
      funext fun i => by rw [coordR, repr_vecOf]
    rw [this, Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  have e : 𝔉.unip hc (AF F) = Subgroup.closure (Mem.UnipCocompact.radSet hc V C d) := by
    rw [← Subgroup.closure_eq (𝔉.unip hc (AF F))]
    congr 1
    ext g
    refine IsoFlag.mem_unip_iff.trans
      (and_congr ⟨fun h i => ?_, fun h i x hx => ?_⟩ ⟨fun h x hx => ?_, fun h x hx => ?_⟩)
    · have := h ⟨d i, hd i⟩ (vecOf V (Cᵀ i)) (by
        rw [hX]; exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
      rw [hX, ← hm] at this
      exact (mem_extSub_span_depth d _ _).1 this
    · rw [hX] at hx ⊢
      refine act_sub_mem_of_mem_span ?_ hx
      rintro _ ⟨j, hj, rfl⟩
      obtain ⟨a, ha, h'⟩ := h j
      exact (mem_extSub_span_depth d _ _).2
        ⟨a, fun l hl => ha l (Nat.le_trans (Nat.lt_succ_iff.1 hj) hl), (hm g _).symm.trans h'⟩
    · rw [ht] at h
      rw [hm]
      exact (mem_extSub_colSpan V _ C _).1 (h _ ((mem_perp_colSpan hc V C _).2 (by simpa only [repr_vecOf] using hx)))
    · rw [ht] at hx ⊢
      have := h _ ((mem_perp_colSpan hc V C _).1 hx)
      rw [hm, show vecOf V (fun i => V.frame.repr x i) = x from V.frame.equivFun.symm_apply_apply x] at this
      exact (mem_extSub_colSpan V _ C _).2 this
  rw [e]
  obtain ⟨K, hK, h⟩ := Mem.UnipCocompact.closure_radSet_cocompact hc V C hC h0 d
  refine ⟨K, hK, fun n => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h n
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

end GlobalTheory.Cusp.FlagCocompact

namespace GlobalTheory.Cusp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cocompact_flag : ∀ (D : D7) (V : HSp D) (𝔉 : IsoFlag V), Cocompact (GQ V) (NA 𝔉) := fun D V 𝔉 => by
  rw [AutFunCompare.GQ_eq]
  exact FlagCocompact.unip_cocompact D.sp.cm 𝔉

end GlobalTheory.Cusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardFrameOfDiagonalStages
section
noncomputable section

namespace GlobalTheory.StdFrameObj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.FWT GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_piT_mul {P : PreCh} (L : LevCh P) :
    (star (L.piT P.u₀ : L.host.E) : L.host.E) * (L.piT P.u₀ : L.host.E) = (L.T P.u₀ : L.host.E) := by
  have h : (star (L.piT P.u₀ : L.host.E) : L.host.E) = L.host.conj (L.piT P.u₀ : L.host.E) :=
    bridge_star_holds P.R L.host _
  rw [h, mul_comm]
  exact L.piT_norm _

def coordPre (P : PreCh) (L : LevCh P) : Pre :=
  Pre.ofCh P L (DiagSp.spacesNorm P.R (host_cmData P.R L.host) (L.T P.u₀) (L.T_prime _) _ (star_piT_mul L)) rfl
    (fun j _ τ => DiagSp.spacesNorm_Y_sig _ _ _ _ _ _ j τ)
    (fun j _ hj => DiagSp.spacesNorm_hasFrame _ _ _ _ _ _ j hj) (fun _ _ _ => rfl)
    (DiagSp.spacesNorm_z_norm _ _ _ _ _ _)

theorem diagSpaces_coordPre (P : PreCh) (L : LevCh P) : DiagSpaces (coordPre P L).sp :=
  DiagSp.spacesNorm_coord _ _ _ _ _ _

end GlobalTheory.StdFrameObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIndexAddOfIsWittLower
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp)
open Module

namespace GlobalTheory.Cusp.WittIdx

section Lin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Formalism.BasicNotions.HSpace E}

theorem mem_perp' {W : Submodule E V.V} {y : V.V} : y ∈ perp V W ↔ ∀ x ∈ W, V.hT x y = 0 := by
  simp only [perp, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem perp_eq_ker_pi_hT_finBasis (A : Submodule E V.V) :
    perp V A = LinearMap.ker (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V)) := by
  ext y
  rw [mem_perp', LinearMap.mem_ker]
  constructor
  · intro h
    funext k
    simpa using h _ (Module.finBasis E A k).2
  · intro h x hx
    have hk : ∀ k, V.hT ((Module.finBasis E A k : A) : V.V) y = 0 := fun k => by
      simpa using congrFun h k
    have hx' : x = ∑ k, (Module.finBasis E A).repr ⟨x, hx⟩ k • ((Module.finBasis E A k : A) : V.V) := by
      have e := congrArg A.subtype ((Module.finBasis E A).sum_repr ⟨x, hx⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Submodule.subtype_apply] at e
      exact e.symm
    rw [hx']
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hk]

private theorem pi_hT_finBasis_range_surjective (A : Submodule E V.V) :
    LinearMap.range (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V)) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := (LinearMap.range (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V))).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
  have hw : ∀ y, V.hT (∑ k, star (φ fun j => if k = j then (1 : E) else 0) •
      ((Module.finBasis E A k : A) : V.V)) y = 0 := by
    intro y
    have h1 := hle ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [LinearMap.pi_apply, smul_eq_mul] at h1
    have h2 : ∑ k, (φ fun j => if k = j then (1 : E) else 0) *
        V.hT ((Module.finBasis E A k : A) : V.V) y = 0 := by
      calc _ = ∑ k, V.hT ((Module.finBasis E A k : A) : V.V) y *
            (φ fun j => if k = j then (1 : E) else 0) := Finset.sum_congr rfl fun k _ => mul_comm _ _
        _ = 0 := h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
    exact h2
  have h0 := V.nondeg.1 _ hw
  have h0' : ∑ k, star (φ fun j => if k = j then (1 : E) else 0) • Module.finBasis E A k = 0 := by
    apply Subtype.ext
    simpa using h0
  have hc : ∀ k, φ (fun j => if k = j then (1 : E) else 0) = 0 := fun k => by
    have := Fintype.linearIndependent_iff.1 (Module.finBasis E A).linearIndependent _ h0' k
    simpa using this
  apply hφ
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp [hc]

theorem finrank_add_finrank_perp (A : Submodule E V.V) : finrank E A + finrank E (perp V A) = V.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun k : Fin (finrank E A) =>
      V.hT ((Module.finBasis E A k : A) : V.V))
  rw [pi_hT_finBasis_range_surjective, finrank_top, Module.finrank_fin_fun, ← perp_eq_ker_pi_hT_finBasis, V.rank_eq] at h
  exact h

end Lin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.Cusp.WittIdx
end

