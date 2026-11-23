module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0080
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfTangentEq
section
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieFaithful

open IsLocalRing

theorem exists_lift_stalk {X : Scheme.{0}} (x : X) {D : CommRingCat.{0}} [IsLocalRing D] (f : Spec D ⟶ X)
    (h : f (closedPoint D) = x) : ∃ ρ : X.presheaf.stalk x ⟶ D, Spec.map ρ ≫ X.fromSpecStalk x = f := by
  subst h
  exact ⟨Scheme.stalkClosedPointTo f, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem stalk_hom_ext {X : Scheme.{0}} (x : X) {D : CommRingCat.{0}} (ρ ρ' : X.presheaf.stalk x ⟶ D)
    (h : Spec.map ρ ≫ X.fromSpecStalk x = Spec.map ρ' ≫ X.fromSpecStalk x) : ρ = ρ' :=
  Spec.map_injective ((cancel_mono _).1 h)

variable {k : Type} [Field k]

section One

variable (G : Over (Sp k)) [GrpObj G]

def unitSec : Sp k ⟶ G.left := (η[G] : 𝟙_ (Over (Sp k)) ⟶ G).left

theorem unitSec_hom : unitSec G ≫ G.hom = 𝟙 _ := Over.w (η[G] : 𝟙_ (Over (Sp k)) ⟶ G)

theorem one_left {T : Over (Sp k)} : (1 : T ⟶ G).left = T.hom ≫ unitSec G := by
  rw [Hom.one_def, Over.comp_left]
  rfl

def origin : G.left := unitSec G (closedPoint k)

abbrev Germ : CommRingCat.{0} := G.left.presheaf.stalk (origin G)

abbrev germMap : Spec (Germ G) ⟶ G.left := G.left.fromSpecStalk (origin G)

def germConst : CommRingCat.of k ⟶ Germ G := Spec.preimage (germMap G ≫ G.hom)

theorem spec_germConst : Spec.map (germConst G) = germMap G ≫ G.hom := Spec.map_preimage _

abbrev germAlg : Algebra k (Germ G) := (germConst G).hom.toAlgebra

attribute [local instance] germAlg

def germEv0 : Germ G ⟶ CommRingCat.of k := (exists_lift_stalk (origin G) (unitSec G) rfl).choose

theorem spec_germEv0 : Spec.map (germEv0 G) ≫ germMap G = unitSec G :=
  (exists_lift_stalk (origin G) (unitSec G) rfl).choose_spec

theorem germConst_germEv0 : germConst G ≫ germEv0 G = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, spec_germConst, ← Category.assoc, spec_germEv0, unitSec_hom, Spec.map_id]

def germEv : Germ G →ₐ[k] k where
  toRingHom := (germEv0 G).hom
  commutes' a := congrArg (fun φ => φ.hom a) (germConst_germEv0 G)

def tanPt (lam : (RingHom.ker (germEv G)).Cotangent →ₗ[k] k) : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ G :=
  Over.homMk (Spec.map (CommRingCat.ofHom (tanHom (germEv G) lam).toRingHom) ≫ germMap G) (by
    dsimp
    rw [Category.assoc, ← spec_germConst, Category.comp_id, ← Spec.map_comp]
    congr 1
    ext a : 2
    exact (tanHom (germEv G) lam).commutes a)

theorem tanPt_left (lam : (RingHom.ker (germEv G)).Cotangent →ₗ[k] k) : (tanPt G lam).left =
    Spec.map (CommRingCat.ofHom (tanHom (germEv G) lam).toRingHom) ≫ germMap G := rfl

theorem one_left_dual : (1 : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ G).left =
    Spec.map (germEv0 G ≫ CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ germMap G := by
  rw [one_left, Spec.map_comp, Category.assoc, spec_germEv0]
  simp

theorem smT_zero_tanPt (lam : (RingHom.ker (germEv G)).Cotangent →ₗ[k] k) :
    smT (𝟙 (Sp k)) 0 (tanPt G lam) = 1 := by
  apply Over.OverMorphism.ext
  rw [smT_left, tanPt_left, one_left_dual, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a : 2
  change epsMul 0 (tanHom (germEv G) lam a) = algebraMap k (DualNumber k) (germEv G a)
  ext
  · simp [epsMul, tanHom_fst, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

end One

theorem exists_germHom {G H : Over (Sp k)} [GrpObj G] [GrpObj H] (g : G ⟶ H) (hg : η[G] ≫ g = η[H]) :
    ∃ ψ : Germ H ⟶ Germ G, Spec.map ψ ≫ germMap H = germMap G ≫ g.left := by
  refine exists_lift_stalk _ _ ?_
  have h : unitSec G ≫ g.left = unitSec H := congrArg (fun φ => φ.left) hg
  have h1 : germMap G (closedPoint (Germ G)) = origin G := Scheme.fromSpecStalk_closedPoint
  change g.left (germMap G (closedPoint (Germ G))) = _
  rw [h1, origin, origin, ← h]
  rfl

attribute [local instance] germAlg

theorem germ_doubling {G : Over (Sp k)} [GrpObj G] (φ : Germ G ⟶ Germ G)
    (hφ : Spec.map φ ≫ germMap G = germMap G ≫ (𝟙 G * 𝟙 G : G ⟶ G).left) (x : Germ G)
    (hx : x ∈ maximalIdeal (Germ G)) : φ.hom x - 2 * x ∈ maximalIdeal (Germ G) ^ 2 := by
  rw [← ker_eq_maximalIdeal_of_algHom (germEv G)] at hx ⊢
  refine mem_sq_of_tanHom_eq_zero _ _ fun lam => ?_
  have h1 : tanPt G lam ≫ (𝟙 G * 𝟙 G : G ⟶ G) = smT (𝟙 (Sp k)) 2 (tanPt G lam) := by
    rw [MonObj.comp_mul, Category.comp_id, ← one_add_one_eq_two, smT_add _ _ (smT_zero_tanPt G lam), smT_unit]
  have h2 := congrArg (fun φ => φ.left) h1
  simp only [Over.comp_left] at h2
  rw [smT_left, tanPt_left, Category.assoc, ← hφ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp] at h2
  have h3 := congrArg (fun ρ => ρ.hom x) (stalk_hom_ext _ _ _ h2)
  change tanHom (germEv G) lam (φ.hom x) = epsMul 2 (tanHom (germEv G) lam x) at h3
  have h0 : germEv G x = 0 := hx
  rw [map_sub, two_mul, map_add (f := _), h3]
  ext
  · simp [epsMul, tanHom_fst, h0]
  · simp [epsMul, two_mul]

theorem germ_sq_of_tan {G H : Over (Sp k)} [GrpObj G] [GrpObj H] (g : G ⟶ H) (ψ : Germ H ⟶ Germ G)
    (hψ : Spec.map ψ ≫ germMap H = germMap G ≫ g.left)
    (hg : ∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ G, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ g = 1) (x : Germ H)
    (hx : x ∈ maximalIdeal (Germ H)) : ψ.hom x ∈ maximalIdeal (Germ G) ^ 2 := by
  rw [← ker_eq_maximalIdeal_of_algHom (germEv H)] at hx
  rw [← ker_eq_maximalIdeal_of_algHom (germEv G)]
  refine mem_sq_of_tanHom_eq_zero _ _ fun lam => ?_
  have h2 := congrArg (fun φ => φ.left) (hg _ (smT_zero_tanPt G lam))
  simp only [Over.comp_left] at h2
  rw [one_left_dual, tanPt_left, Category.assoc, ← hψ, ← Category.assoc, ← Spec.map_comp] at h2
  have h3 := congrArg (fun ρ => ρ.hom x) (stalk_hom_ext _ _ _ h2)
  change tanHom (germEv G) lam (ψ.hom x) = algebraMap k (DualNumber k) (germEv H x) at h3
  have h0 : germEv H x = 0 := hx
  rw [h3, h0, map_zero]

theorem germMap_comp_eq_one {G H : Over (Sp k)} [GrpObj G] [GrpObj H] (g : G ⟶ H) (ψ : Germ H ⟶ Germ G)
    (hψ : Spec.map ψ ≫ germMap H = germMap G ≫ g.left)
    (h0 : ∀ x ∈ maximalIdeal (Germ H), ψ.hom x = 0) :
    germMap G ≫ g.left = germMap G ≫ (1 : G ⟶ H).left := by
  have hc : germConst H ≫ ψ = germConst G := by
    apply Spec.map_injective
    rw [Spec.map_comp, spec_germConst, spec_germConst, ← Category.assoc, hψ, Category.assoc, Over.w]
  have he : ψ = germEv0 H ≫ germConst G := by
    ext x : 2
    have h1 : x - algebraMap k (Germ H) (germEv H x) ∈ maximalIdeal (Germ H) := by
      rw [← ker_eq_maximalIdeal_of_algHom (germEv H)]
      exact (kerPart (germEv H) x).2
    have h2 := h0 _ h1
    rw [map_sub, sub_eq_zero] at h2
    rw [h2]
    exact congrArg (fun ρ => ρ.hom (germEv H x)) hc
  rw [← hψ, he, Spec.map_comp, Category.assoc, spec_germEv0, spec_germConst, one_left, Category.assoc]

theorem hom_eq_of_tangent_eq : ∀ (k : Type) [Field k] [CharZero k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (f f' : A ⟶ B) [IsMonHom f] [IsMonHom f'], (∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ A, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ f = v ≫ f') → f = f' := by
  intro k _ _ A B _ _ _ _ hA hB f f' _ _ h
  have hint := GlobalTheory.isIntegral_left_of_isAbelianScheme_field A hA
  have := hA.proper
  have := hB.proper
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let g : A ⟶ B := f * f'⁻¹
  have hu : IsMonHom g := by
    simp only [g]
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  have hg : ∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ A, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ g = 1 := fun v hv => by
    simp only [g]
    rw [MonObj.comp_mul, GrpObj.comp_inv, h v hv, mul_inv_cancel]
  have h2 : ∀ (G : Over (Sp k)) [GrpObj G], η[G] ≫ (𝟙 G * 𝟙 G : G ⟶ G) = η[G] := fun G _ => by
    have e : (η[G] : 𝟙_ (Over (Sp k)) ⟶ G) = 1 := by simp [Hom.one_def]
    rw [MonObj.comp_mul, Category.comp_id, e, _root_.mul_one]
  obtain ⟨ψ, hψ⟩ := exists_germHom g (IsMonHom.one_hom g)
  obtain ⟨φA, hφA⟩ := exists_germHom _ (h2 A)
  obtain ⟨φB, hφB⟩ := exists_germHom _ (h2 B)
  have hcomm : (𝟙 A * 𝟙 A : A ⟶ A) ≫ g = g ≫ (𝟙 B * 𝟙 B : B ⟶ B) := by
    rw [MonObj.mul_comp, MonObj.comp_mul g, Category.comp_id, Category.id_comp]
  have hcomm' : (𝟙 A * 𝟙 A : A ⟶ A).left ≫ g.left = g.left ≫ (𝟙 B * 𝟙 B : B ⟶ B).left :=
    congrArg (fun φ => φ.left) hcomm
  have hc : φB ≫ ψ = ψ ≫ φA := by
    apply stalk_hom_ext
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hφB, hψ, ← Category.assoc, hψ,
      ← Category.assoc, hφA, Category.assoc, Category.assoc, hcomm']
  have h0 := map_eq_zero_of_commute_doubling (k := k) (maximalIdeal (Germ B)) φA.hom φB.hom ψ.hom
    (fun x => congrArg (fun ρ => ρ.hom x) hc) (germ_sq_of_tan g ψ hψ hg) (germ_doubling φA hφA)
    (germ_doubling φB hφB)
  have h3 := germMap_comp_eq_one g ψ hψ h0
  have : IsDominant (germMap A) := ⟨by
    refine dense_iff_closure_eq.2 (top_unique ((genericPoint_spec A.left).def.ge.trans
      (closure_mono (Set.singleton_subset_iff.2 ?_))))
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes _⟩
  have h4 : g = 1 := Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated B.hom ((Over.w _).trans (Over.w _).symm) (germMap A) h3)
  exact mul_inv_eq_one.1 h4

end GlobalTheory.LieFaithful
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H
open scoped BigOperators
open Classical

namespace GlobalTheory.BaseVacuum

def four : Fin 4 ≃ Fin 2 × Fin 2 := (finCongr (by norm_num)).trans finProdFinEquiv.symm

def posE (n n' : ℕ) : (Fin n' × Fin n) × Fin 4 ≃ Fin (n' * 2) × Fin (n * 2) :=
  ((Equiv.refl _).prodCongr four).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans (finProdFinEquiv.prodCongr finProdFinEquiv))

abbrev Ix (D : D7) (n n' : ℕ) : Type := (Fin n' × Fin n) × (Fin 4 × D.what₂.Tau)

def blk (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) : Fin 4 × D.what₂.Tau → ℂ :=
  fun w => z w.2 (posE n n' (k, w.1)).1 (posE n n' (k, w.1)).2

def reix (D : D7) (n n' : ℕ) : TaylorLogMetric.VC D (n * 2) (n' * 2) ≃ₗ[ℂ] (Ix D n n' → ℂ) where
  toFun z p := blk D p.1 z p.2
  invFun y τ i j := y (((posE n n').symm (i, j)).1, (((posE n n').symm (i, j)).2, τ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    funext τ i j
    simp [blk]
  right_inv y := by
    funext p
    simp [blk]

def gBig {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    (Ix D n n' → ℂ) ≃ₗ[ℂ] (Ix D n n' → ℂ) where
  toFun y p := B.gC (fun w => y (p.1, w)) p.2
  invFun y p := B.gC.symm (fun w => y (p.1, w)) p.2
  map_add' x y := by
    funext p
    show B.gC ((fun w => x (p.1, w)) + (fun w => y (p.1, w))) p.2 = _
    rw [map_add (f := _)]; rfl
  map_smul' c x := by
    funext p
    show B.gC (c • (fun w => x (p.1, w))) p.2 = _
    rw [map_smul]; rfl
  left_inv y := by
    funext p
    simp
  right_inv y := by
    funext p
    simp

def phi {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    TaylorLogMetric.VC D (n * 2) (n' * 2) ≃ₗ[ℂ] (Ix D n n' → ℂ) :=
  (reix D n n').trans (gBig B n n')

theorem phi_apply {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ)
    (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) (p : Ix D n n') : phi B n n' z p = B.gC (blk D p.1 z) p.2 := rfl

def ixE (D : D7) (n n' : ℕ) : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2)) ≃ Ix D n n' :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin]
    simp only [Fintype.card_prod, Fintype.card_fin, D.what₂.card_Tau, TaylorLogMetric.fF]
    ring)

def xv {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) : Fin 4 → D.host.E :=
  B.γ₀.g.symm (Pi.single w 1)

def putB (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (x : Fin 4 → D.host.E) :
    Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E :=
  fun i j => if ((posE n n').symm (i, j)).1 = k then x ((posE n n').symm (i, j)).2 else 0

def bas {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2)) → Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E :=
  fun j => putB D (ixE D n n' j).1 (xv B (ixE D n n' j).2)

def blkLat {ι m : Type} (Λ : AddSubgroup (m → ℂ)) : AddSubgroup (ι × m → ℂ) where
  carrier := {y | ∀ k, (fun w => y (k, w)) ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy k => Λ.add_mem (hx k) (hy k)
  neg_mem' := fun hx k => Λ.neg_mem (hx k)

end GlobalTheory.BaseVacuum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalMulVecApply
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory.OrthSumGram

open Matrix

theorem blockDiagonal'_mulVec_apply' {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (M : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (u : (Σ i, Fin (n i)) → ℂ) (i : ι) (j : Fin (n i)) :
    (blockDiagonal' M *ᵥ u) ⟨i, j⟩ = (M i *ᵥ fun l => u ⟨i, l⟩) j := by
  simp only [mulVec, dotProduct, Fintype.sum_sigma, blockDiagonal'_apply]
  rw [Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp
  · intro k _ hk
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [dite_eq_right (Ne.symm hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem orth_sum_hasGram : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (ι : Type) [Fintype ι] (N : (K →+* ℂ) → V → ℝ) (W : ι → Submodule K V), (∀ σ x, 0 ≤ N σ x) → iSupIndep W → ⨆ i, W i = ⊤ → (∀ i, HasGram (fun σ (x : W i) => N σ x)) → (∀ σ, ∀ f : ∀ i, W i, N σ (∑ i, (f i : V)) ^ 2 = ∑ i, N σ (f i) ^ 2) → HasGram N := by
  classical
  intro K V _ _ _ _ ι _ N W hN hind htop hG hpy
  have hint : DirectSum.IsInternal W :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).2 ⟨hind, htop⟩
  let g := fun i => (hG i).some
  let n : ι → ℕ := fun i => (g i).1
  let b : ∀ i, Module.Basis (Fin (n i)) K (W i) := fun i => (g i).2.1.1
  let X : ∀ i, InfinitePlace K → Matrix (Fin (n i)) (Fin (n i)) ℂ := fun i => (g i).2.1.2
  have hX : ∀ i, IsGram (b i) (X i) (fun σ (x : W i) => N σ x) := fun i => (g i).2.2
  let B := hint.collectedBasis b
  have hB : ∀ a, B a = (b a.1 a.2 : V) := fun a => by
    simp only [B, DirectSum.IsInternal.collectedBasis_coe]
  let Xv : InfinitePlace K → Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℂ := fun v => blockDiagonal' fun i => X i v
  have hmul : ∀ v, Xv v * blockDiagonal' (fun i => (X i v)⁻¹) = 1 := fun v => by
    simp only [Xv, ← blockDiagonal'_mul]
    rw [← blockDiagonal'_one]
    congr 1
    funext i
    exact Matrix.mul_nonsing_inv _ ((hX i v).1)
  refine IsGram.hasGram (b := B) (X := Xv) fun v => ⟨Matrix.isUnit_det_of_right_inverse (hmul v), fun x => ?_⟩
  have hinv : (Xv v)⁻¹ = blockDiagonal' (fun i => (X i v)⁻¹) := Matrix.inv_eq_right_inv (hmul v)
  let c := B.repr x
  let f : ∀ i, W i := fun i => ∑ j, c ⟨i, j⟩ • b i j
  have hx : x = ∑ i, (f i : V) := by
    conv_lhs => rw [← B.sum_repr x]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [f, Submodule.coe_sum, Submodule.coe_smul, hB]
    rfl
  have hrep : ∀ i j, (b i).repr (f i) j = c ⟨i, j⟩ := fun i j => by
    simp only [f, Module.Basis.repr_sum_self]
  have hcoord : ∀ i j, Formalism.HermitianLatticesTheory.fcoord B Xv v x ⟨i, j⟩ = Formalism.HermitianLatticesTheory.fcoord (b i) (X i) v (f i) j := fun i j => by
    simp only [Formalism.HermitianLatticesTheory.fcoord, hinv, blockDiagonal'_mulVec_apply']
    congr 1
    funext l
    simp only [Formalism.HermitianLatticesTheory.vecAt, hrep, c]
  have hsq : Formalism.HermitianLatticesTheory.normAt B Xv v x ^ 2 = N v.embedding x ^ 2 := by
    rw [hx, hpy, ← hx]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : Formalism.HermitianLatticesTheory.normAt (b i) (X i) v (f i) = N v.embedding (f i) := (hX i v).2 (f i)
    rw [← e]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoord]
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt B Xv v x := Real.sqrt_nonneg _
  exact (sq_eq_sq₀ h0 (hN _ _)).1 hsq

end GlobalTheory.OrthSumGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTwistNonzeroLocusMaps
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace TwistCube

open Twist

variable {X : Scheme.{0}} (F : X.Modules) {L : LB X}

theorem mulSecOfEq_zpowSec_comp (σ : LB.Sec (lbZPow L 1)) {n d e : ℤ} (a b : ℕ)
    (h₁ : n + a * 1 = d) (h₂ : d + b * 1 = e) (h₃ : n + ((a + b : ℕ) : ℤ) * 1 = e) :
    mulSecOfEq F (zpowSec σ a) h₁ ≫ mulSecOfEq F (zpowSec σ b) h₂ =
      mulSecOfEq F (zpowSec σ (a + b)) h₃ := by
  ext V s : 3
  exact mulSecOfEq_zpowSec_app σ rfl h₁ h₂ h₃ s

def powMap (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) : F ⟶ twistZ F L c :=
  (twistZZeroIso F hL).hom ≫ mulSecOfEq F (zpowSec σ c) (by omega)

theorem powMap_comp (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (j c d : ℕ) (h : c + j = d)
    (h' : (c : ℤ) + (j : ℤ) * 1 = d) :
    powMap F hL σ c ≫ mulSecOfEq F (zpowSec σ j) h' = powMap F hL σ d := by
  subst h
  rw [powMap, powMap, Category.assoc, mulSecOfEq_zpowSec_comp F σ c j _ _ (by push_cast; ring)]

theorem bijective_powMap_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {W : X.Opens}
    (hW : W ≤ nonzeroLocus σ) : Function.Bijective ((powMap F hL σ c).app W) := by
  rw [powMap, Scheme.Modules.Hom.comp_app, ConcreteCategory.coe_comp]
  exact (bijective_mulSecOfEq_app hL _ (by omega) (hW.trans (nonzeroLocus_le_zpowSec hL σ c))).comp
    (ConcreteCategory.bijective_of_isIso ((twistZZeroIso F hL).hom.app W))

variable {ι : Type} (U : ι → X.Opens)

theorem isIso_cechCubeMap_powMap (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : IsIso (cechCubeMap ℤ V U (powMap F hL σ c)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun s => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_powMap_app F hL σ c ((cechOpen_le V U s).trans hV)

theorem cechCubeRes_naturality {G : X.Modules} (φ : F ⟶ G) {V : X.Opens} :
    cechCubeMap ℤ ⊤ U φ ≫ cechCubeRes ℤ G (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) =
      cechCubeRes ℤ F (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) ≫ cechCubeMap ℤ V U φ :=
  presheafCubeRes_naturality (sectionsPresheafMap ℤ φ) _

def cubeDiv (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F V U :=
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) ≫
    inv (cechCubeMap ℤ V U (powMap F hL σ c))

theorem cubeDiv_comp (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : cubeDiv F U hL σ c hV ≫ cechCubeMap ℤ V U (powMap F hL σ c) =
      cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) := by
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  simp [cubeDiv]

theorem cubeDiv_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) (s : Finset ι) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s) :
    (cechCubeMap ℤ V U (powMap F hL σ c)).app s ((cubeDiv F U hL σ c hV).app s a) =
      (cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)).app s a := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, cubeDiv_comp]

theorem cechCubeMap_mul_comp_cubeDiv (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (j c d : ℕ)
    (h : c + j = d) (h' : (c : ℤ) + (j : ℤ) * 1 = d) {V : X.Opens} (hV : V ≤ nonzeroLocus σ) :
    cechCubeMap ℤ ⊤ U (mulSecOfEq F (zpowSec σ j) h') ≫ cubeDiv F U hL σ d hV =
      cubeDiv F U hL σ c hV := by
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  haveI := isIso_cechCubeMap_powMap F U hL σ d hV
  unfold cubeDiv
  rw [← Category.assoc, cechCubeRes_naturality, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, IsIso.eq_inv_comp]
  exact congrArg (cechCubeMap ℤ V U) (powMap_comp F hL σ j c d h h')

end TwistCube

end GlobalTheory

theorem GlobalTheory.cechCube_nonzeroLocus_colimit : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens), (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∃ (μ : ∀ (j c d : ℕ), c + j = d → (cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ (twistZ F L d) ⊤ U)) (ρ : ∀ c : ℕ, cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F (nonzeroLocus σ) U), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) ∧ (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') ∧ (∀ s : Finset ι, s.Nonempty → ∀ b : (cechCube ℤ F (nonzeroLocus σ) U).obj s, ∃ c : ℕ, ∃ a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s, (ρ c).app s a = b) ∧ (∀ s : Finset ι, s.Nonempty → ∀ (c : ℕ) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) := by
  intro X F _ L hL σ₀ ι _ _ U hU
  have hVσ : nonzeroLocus σ₀ ≤ nonzeroLocus (Twist.zofSec σ₀) := (Twist.nonzeroLocus_zofSec hL σ₀).ge
  refine ⟨fun j c d h => cechCubeMap ℤ ⊤ U
      (Twist.mulSecOfEq F (Twist.zpowSec (Twist.zofSec σ₀) j) (by omega)),
    fun c => TwistCube.cubeDiv F U hL (Twist.zofSec σ₀) c hVσ, ?_, ?_, ?_, ?_⟩
  · intro j c d h
    exact TwistCube.cechCubeMap_mul_comp_cubeDiv F U hL _ j c d h _ hVσ
  · intro j j' c d e h h' h''
    exact congrArg (cechCubeMap ℤ ⊤ U) (TwistCube.mulSecOfEq_zpowSec_comp F _ j j' (by omega) _ _)
  · intro s hs b
    have hA : IsAffineOpen (cechOpen ⊤ U s) := by rw [cechOpen_top]; exact hU s hs
    have hle : cechOpen (nonzeroLocus σ₀) U s ≤ cechOpen ⊤ U s :=
      cechOpen_mono le_top (fun _ => le_rfl) s
    have hV : cechOpen (nonzeroLocus σ₀) U s =
        cechOpen ⊤ U s ⊓ nonzeroLocus (Twist.zofSec σ₀) := by
      rw [cechOpen, cechOpen, top_inf_eq, Twist.nonzeroLocus_zofSec hL, inf_comm]
    obtain ⟨k, hk⟩ := (Twist.eventually_exists_resM_eq_mulSecOfEq_zpowSec hL (Twist.zofSec σ₀)
      hA.isCompact hA.isQuasiSeparated hle hV ((Twist.twistZZeroIso F hL).hom.app _ b)).exists
    obtain ⟨a, ha⟩ := hk k (by omega)
    exact ⟨k, a, (TwistCube.bijective_powMap_app F hL _ k ((cechOpen_le _ U s).trans hVσ)).1
      ((TwistCube.cubeDiv_app F U hL (Twist.zofSec σ₀) k hVσ s a).trans ha)⟩
  · intro s hs c a ha
    have hA : IsAffineOpen (cechOpen ⊤ U s) := by rw [cechOpen_top]; exact hU s hs
    have hle : cechOpen (nonzeroLocus σ₀) U s ≤ cechOpen ⊤ U s :=
      cechOpen_mono le_top (fun _ => le_rfl) s
    have hV : cechOpen (nonzeroLocus σ₀) U s =
        cechOpen ⊤ U s ⊓ nonzeroLocus (Twist.zofSec σ₀) := by
      rw [cechOpen, cechOpen, top_inf_eq, Twist.nonzeroLocus_zofSec hL, inf_comm]
    have h0 : Twist.resM _ hle a = 0 := by
      have e := TwistCube.cubeDiv_app F U hL (Twist.zofSec σ₀) c hVσ s a
      rw [ha, map_zero] at e
      exact e.symm
    obtain ⟨k, hk⟩ := (Twist.eventually_mulSecOfEq_zpowSec_eq_zero hL (Twist.zofSec σ₀)
      hA.isCompact hle hV.ge a h0).exists
    exact ⟨k, hk _ (by push_cast; ring)⟩
end
end

