module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0593
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0116
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelOfMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.Per

namespace GlobalTheory.CrysSubRep

variable {l : ℕ} [Fact l.Prime]

def entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) : FinExt l :=
  ⟨L.1 ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : Fin d × Fin a => M p.1 p.2),
    haveI := L.2
    haveI : FiniteDimensional ℚ_[l]
        (IntermediateField.adjoin ℚ_[l] (Set.range fun p : Fin d × Fin a => M p.1 p.2)) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    IntermediateField.finiteDimensional_sup _ _⟩

theorem le_entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) :
    L.1 ≤ (entExt L M).1 := le_sup_left

theorem mem_entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) (i : Fin d) (j : Fin a) :
    M i j ∈ (entExt L M).1 :=
  (le_sup_right : IntermediateField.adjoin ℚ_[l] _ ≤ (entExt L M).1)
    (IntermediateField.subset_adjoin _ _ ⟨(i, j), rfl⟩)

theorem exists_leftInv {K : Type} [Field K] {d a : ℕ} (M : Matrix (Fin d) (Fin a) K)
    (h : Function.Injective M.mulVec) : ∃ N : Matrix (Fin a) (Fin d) K, N * M = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' M)
    (LinearMap.ker_eq_bot.2 (by rw [Matrix.toLin'_apply', Matrix.coe_mulVecLin]; exact h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' M, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem exists_model_of_mem {Γ : Type} [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) (Om l)) (L : FinExt l)
    (hL : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : Γ →* GL (Fin a) ↥L.1, Formalism.MainNotions.N.mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : Γ → Matrix (Fin a) (Fin a) ↥L.1 :=
    fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : Γ →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  exact ⟨ρ, MonoidHom.ext fun g => Units.ext (hM g)⟩

end GlobalTheory.CrysSubRep

namespace GlobalTheory.CrysSubRep

theorem isCrysAt_of_sub : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (d a : ℕ) (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℚ_[l])
    (r : ↥Gw →* GL (Fin a) (Om l)),
    IsCrys (P.PD Bw.Kw) (((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp ((Units.coeHom _).comp ρ) : Representation ℚ_[l] ↥(GK Bw.Kw) (Fin d → ℚ_[l])) →
    ∀ M : Matrix (Fin d) (Fin a) (Om l), Function.Injective M.mulVec →
    (∀ g : ↥Gw, ((ρ (Bw.e g) : GL (Fin d) ℚ_[l]) : Matrix (Fin d) (Fin d) ℚ_[l]).map (algebraMap ℚ_[l] (Om l)) * M =
      M * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) →
    GlobalTheory.Pst.IsCrysAt P Bw r := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw d a ρ r hρ M hM hint
  obtain ⟨T⟩ := hT
  let L : FinExt l := entExt Bw.LL M
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M' : Matrix (Fin d) (Fin a) ↥L.1 := Matrix.of fun i j => ⟨M i j, mem_entExt Bw.LL M i j⟩
  have hM' : M'.map f = M := Matrix.ext fun i j => rfl
  have hinjM' : Function.Injective M'.mulVec := by
    intro x y hxy
    have h1 : ∀ v : Fin a → ↥L.1, M.mulVec (fun i => f (v i)) = fun i => f (M'.mulVec v i) :=
      fun v => funext fun i => by rw [← hM']; exact (RingHom.map_mulVec f M' v i).symm
    have h2 := hM (show M.mulVec (fun i => f (x i)) = M.mulVec (fun i => f (y i)) by rw [h1, h1, hxy])
    exact funext fun i => f.injective (congrFun h2 i)
  obtain ⟨N, hN⟩ := exists_leftInv M' hinjM'
  let ρL : ↥(GK Bw.Kw) →* Matrix (Fin d) (Fin d) ↥L.1 :=
    (RingHom.mapMatrix (algebraMap ℚ_[l] ↥L.1)).toMonoidHom.comp ((Units.coeHom _).comp ρ)
  have hmapρ : ∀ g, ((ρ g : GL (Fin d) ℚ_[l]) : Matrix (Fin d) (Fin d) ℚ_[l]).map (algebraMap ℚ_[l] (Om l)) =
      (ρL g).map f := fun g => by
    simp only [ρL, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      Units.coeHom_apply, Matrix.map_map]
    congr 1
  have hint' : ∀ g, (ρL (Bw.e g)).map f * M'.map f = M'.map f * (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => by
    rw [← hmapρ, hM']; exact hint g
  have hr : ∀ g, (r g : Matrix (Fin a) (Fin a) (Om l)) = (N * ρL (Bw.e g) * M').map f := fun g => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, hint', ← Matrix.mul_assoc, ← Matrix.map_mul, hN,
      Matrix.map_one f (map_zero f) (map_one f), Matrix.one_mul]
  have hmem : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := fun g i j => by
    rw [hr g]; exact ((N * ρL (Bw.e g) * M') i j).2
  obtain ⟨r', hr'⟩ := exists_model_of_mem r L hmem
  have hmod : GlobalTheory.Pst.IsModel Bw r L r' := ⟨le_entExt Bw.LL M, hr'⟩
  have hr'g : ∀ g, ((r' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1).map f =
      (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => by
    rw [← hr']; rfl
  have hinjMap : ∀ {m n : ℕ}, Function.Injective (fun X : Matrix (Fin m) (Fin n) ↥L.1 => X.map f) :=
    fun {m n} X Y h => Matrix.ext fun i j => f.injective (congrFun (congrFun h i) j)
  have hintL : ∀ g, ρL (Bw.e g) * M' = M' * (r' g : Matrix (Fin a) (Fin a) ↥L.1) := fun g =>
    hinjMap (by simp only [Matrix.map_mul]; rw [hr'g]; exact hint' g)
  haveI := L.2
  have hcL : IsCrys (P.PD Bw.Kw) (Formalism.MainNotions.N.matRep ρL) :=
    (GlobalTheory.Pst.isCrys_ext_iff (P.PD Bw.Kw) (fun g => ⟨(ρ g : Matrix (Fin d) (Fin d) ℚ_[l]), fun x => rfl, fun x => rfl⟩)).2 hρ
  refine ⟨L, r', hmod, ?_⟩
  refine GlobalTheory.TateDualCrys.isCrys_of_isSubOfSums T Bw.Kw L (ι := Unit) (fun _ => ρL) (fun _ => hcL) (Fin a → ↥L.1)
    (Bw.repE L r') ⟨1, fun _ => (), LinearMap.pi (fun _ => Matrix.toLin' M'), fun x y h => hinjM' (congrFun h 0), ?_⟩
  intro g v
  funext i
  have e1 := hintL (Bw.e.symm g)
  rw [MulEquiv.apply_symm_apply] at e1
  show M'.mulVec ((r' (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1).mulVec v) = (ρL g).mulVec (M'.mulVec v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1]

end GlobalTheory.CrysSubRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdempotentMatrixLocalRingMapField
section
open Matrix

namespace GlobalTheory.IdemRankLocal

theorem exists_conj_diag (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ)
    (p : Matrix (Fin n) (Fin n) W) (hp : p * p = p) :
    ∃ (r : ℕ) (P P' : Matrix (Fin n) (Fin n) W), P * P' = 1 ∧
    p = P * Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) * P' := by
  classical
  set f : (Fin n → W) →ₗ[W] (Fin n → W) := Matrix.toLin' p with hfdef
  have hf : IsIdempotentElem f := by
    show f * f = f
    rw [Module.End.mul_eq_comp, hfdef, ← Matrix.toLin'_mul, hp]
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  haveI : Module.Projective W (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc x)
  haveI : Module.Projective W (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm x)
  haveI : Module.Finite W (LinearMap.range f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc)
      (Submodule.linearProjOfIsCompl_surjective hc)
  haveI : Module.Finite W (LinearMap.ker f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (Submodule.linearProjOfIsCompl_surjective hc.symm)
  haveI : Module.Free W (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free W (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  set r := Module.finrank W (LinearMap.range f)
  set s := Module.finrank W (LinearMap.ker f)
  let b1 := Module.finBasis W (LinearMap.range f)
  let b2 := Module.finBasis W (LinearMap.ker f)
  let bs : Module.Basis (Fin r ⊕ Fin s) W (Fin n → W) :=
    (b1.prod b2).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hrs : r + s = n := by
    have := Module.finrank_eq_card_basis bs
    simpa [Fintype.card_sum] using this.symm
  have hbs1 : ∀ i, f (bs (Sum.inl i)) = bs (Sum.inl i) := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
    obtain ⟨y, hy⟩ := (b1 i).2
    rw [← hy]
    exact LinearMap.congr_fun hf y
  have hbs2 : ∀ i, f (bs (Sum.inr i)) = 0 := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
  let b : Module.Basis (Fin n) W (Fin n → W) := bs.reindex (finSumFinEquiv.trans (finCongr hrs))
  have hb : ∀ j : Fin n, f (b j) = (if j.val < r then (1 : W) else 0) • b j := by
    intro j
    have hj : b j = bs ((finSumFinEquiv.trans (finCongr hrs)).symm j) := Module.Basis.reindex_apply _ _ _
    rw [hj]
    by_cases h : j.val < r
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inl ⟨j, h⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp
      rw [this, if_pos h, one_smul, hbs1]
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inr ⟨j.val - r, by omega⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp; omega
      rw [this, if_neg h, zero_smul, hbs2]
  have hdiag : LinearMap.toMatrix b b f = Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, b.repr_self]
    by_cases hij : i = j
    · subst hij; simp; split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ hij, Finsupp.single_apply, Ne.symm hij]
      split_ifs <;> simp [Finsupp.single_apply, Ne.symm hij]
  let e := Pi.basisFun W (Fin n)
  refine ⟨r, e.toMatrix b, b.toMatrix e, ?_, ?_⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip e b
  · have := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e b e b f
    rw [← hdiag, this, LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']

theorem rank_map_const : ∀ (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ) (Q : Matrix (Fin n) (Fin n) W),
    Q * Q = Q → ∃ r : ℕ, ∀ (k : Type) [Field k] (β : W →+* k), (Q.map β).rank = r := by
  intro W _ _ n Q hQ
  classical
  obtain ⟨r, P, P', hPP', hQeq⟩ := exists_conj_diag W n Q hQ
  refine ⟨Fintype.card {i : Fin n // i.val < r}, fun k _ β => ?_⟩
  have hm : P.map β * P'.map β = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ β.map_zero β.map_one]
  have hP : IsUnit (P.map β).det := Matrix.isUnit_det_of_right_inverse hm
  have hP' : IsUnit (P'.map β).det := Matrix.isUnit_det_of_left_inverse hm
  rw [hQeq, Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hP',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP, Matrix.diagonal_map β.map_zero,
    Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by split_ifs with h <;> simp [h]))

end GlobalTheory.IdemRankLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelDimOfIsSemiAbelian
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbelianDim

theorem exists_relDim_of_isSemiAbelian : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro R _ _ G _ _ hG
  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Sp R) := AbelianDim.connectedSpace_spec_of_isLocalRing R
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group _ G).1
  obtain ⟨x⟩ : Nonempty G.left := inferInstance
  exact exists_dim_of_preconnected G.hom x

end GlobalTheory.SemiAbelianDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemes
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActPull

theorem exists_act_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∃ act' : O → (G' ⟶ G'), ((∀ a, IsMonHom (act' a)) ∧ act' 1 = 𝟙 G' ∧ (∀ a b, act' (a * b) = act' a ≫ act' b) ∧ (∀ a b, act' (a + b) = act' a * act' b)) ∧ ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := by
  intro S S' f G _ G' _ φ hg O _ act hhom hone hmul hadd
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act' : O → (G' ⟶ G') := fun a => Over.homMk (hg.1.lift (φ ≫ (act a).left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G') a, pushPt hg.1.w (x ≫ act' a) = pushPt hg.1.w x ≫ act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨act', ⟨fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩, ha⟩
  · have := hhom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act' 1), pa, hone, Category.comp_id]
  · rw [← Category.id_comp (act' (a * b)), pa, pa, hmul, ← Category.id_comp (act' a), pa, Category.assoc]
  · refine Eq.trans ?_ (pm (act' a) (act' b)).symm
    rw [← Category.id_comp (act' (a + b)), ← Category.id_comp (act' a), ← Category.id_comp (act' b), pa, pa, pa, hadd]
    exact MonObj.comp_mul _ _ _

end GlobalTheory.ActPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetChar

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

section Alg

variable {R : Type} [CommRing R]

def cut (a : R) (ha : a * a = a) : Rˣ →* Rˣ where
  toFun u := ⟨a * u + (1 - a), a * (u⁻¹ : Rˣ) + (1 - a),
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv,
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv⟩
  map_one' := Units.ext (by simp)
  map_mul' u w := Units.ext (by
    show a * ((u : R) * w) + (1 - a) = (a * u + (1 - a)) * (a * w + (1 - a))
    linear_combination (-((u : R) * w) + u + w - 1) * ha)

theorem cut_val (a : R) (ha : a * a = a) (u : Rˣ) : (cut a ha u : R) = a * u + (1 - a) := rfl

theorem continuous_cut [TopologicalSpace R] [IsTopologicalRing R] (a : R) (ha : a * a = a) :
    Continuous (cut a ha) :=
  Units.continuous_iff.2 ⟨(continuous_const.mul Units.continuous_val).add continuous_const,
    (continuous_const.mul Units.continuous_coe_inv).add continuous_const⟩

theorem mul_det {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, a * (M - 1) i j = 0) :
    a * M.det = a := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R a)
  have hI : ∀ x, x ∈ I ↔ x * a = 0 := fun x => Iff.rfl
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 ((hI _).2 ((mul_comm _ _).trans (h i j)))
  have h2 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, h1, map_one, det_one, map_one]
  have h3 := (hI _).1 (Ideal.Quotient.eq.1 h2)
  linear_combination h3

end Alg


theorem char_norm {D : D7} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n)
    (x y : (Formalism.L2.Theta.AE D)ˣ) (hy : (y : Formalism.L2.Theta.AE D) = x * cA D x) : χ y = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := h
  have := D.host.isCMField_hostE
  have e : y = idF D (Units.map (Algebra.norm (AF D.host.F) : Formalism.L2.Theta.AE D →* AF D.host.F) x) :=
    Units.ext (hy.trans (GlobalTheory.Published.algebraMap_norm_tensor (E := D.host.E) (AF D.host.F)
      (x : Formalism.L2.Theta.AE D)).symm)
  rw [e, h η hη, hη.2.2.1, one_pow]


end GlobalTheory.SplitDetChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareGroupSchemePullback
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqPull

theorem tensor_isPullback {S : Scheme.{0}} (X Y : Over S) :
    IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := by
  rw [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback _ _

theorem sq_of_grpPullback : ∀ (S S₀ : Scheme.{0}) (f : S₀ ⟶ S) (B : Over S) [GrpObj B] (B₀ : Over S₀) [GrpObj B₀] (i : B₀.left ⟶ B.left), IsGrpPullback B₀ B f i → ∃ k : (B₀ ⊗ B₀).left ⟶ (B ⊗ B).left, IsPullback k (B₀ ⊗ B₀).hom (B ⊗ B).hom f ∧ k ≫ (μ[B]).left = (μ[B₀]).left ≫ i ∧ k ≫ (fst B B).left = (fst B₀ B₀).left ≫ i ∧ k ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
  intro S S₀ f B _ B₀ _ i h
  obtain ⟨hP, hM⟩ := h
  let T : Over S₀ := B₀ ⊗ B₀
  have hw : ∀ x : T ⟶ B₀, (x.left ≫ i) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
    intro x
    rw [Category.assoc, hP.w, ← Category.assoc, Over.w x]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((fst B₀ B₀).left ≫ i) (hw _)
  let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((snd B₀ B₀).left ≫ i) (hw _)
  have h1 : (lift x₀ y₀).left ≫ (fst B B).left = (fst B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h2 : (lift x₀ y₀).left ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  refine ⟨(lift x₀ y₀).left, ?_, ?_, h1, h2⟩
  · have outer : IsPullback ((snd B₀ B₀).left ≫ i) (fst B₀ B₀).left B.hom (B₀.hom ≫ f) :=
      IsPullback.paste_horiz (tensor_isPullback B₀ B₀).flip hP
    have sq : IsPullback (lift x₀ y₀).left (fst B₀ B₀).left (fst B B).left i := by
      refine IsPullback.of_right (h₁₂ := (snd B B).left) (v₁₃ := B.hom) (h₂₂ := B.hom) ?_ h1
        (tensor_isPullback B B).flip
      rw [h2, hP.w]
      exact outer
    exact IsPullback.paste_vert sq hP
  · have := hM T (fst B₀ B₀) (snd B₀ B₀) x₀ y₀ rfl rfl
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at this
    exact this

end GlobalTheory.SqPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTqLevelZeroOfTorusExtension
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Raynaud

theorem exists_tq_level_zero_of_torusExtension : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G], Nonempty (TorusExtension ((Over.pullback (spMap (residue R))).obj G)) →
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X),
      Nonempty (TQ (thickObj R (maximalIdeal R) 0 G) X) := by
  intro R _ _ G _ _ hT
  obtain ⟨E, ⟨d⟩⟩ := exists_splitExt_isGt_of_torusExtension (ResidueField R) _ hT
  have := E.free
  have := E.finite
  refine ⟨E.X, inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨Q₁, -⟩ := exists_tq_of_gtDatum _ E _ d
  let r : Sp (R ⧸ maximalIdeal R ^ (0 + 1)) ⟶ Sp (ResidueField R) :=
    spMap (Ideal.Quotient.factor (show maximalIdeal R ≤ maximalIdeal R ^ (0 + 1) by simp))
  have hr : r ≫ spMap (residue R) = thick R (maximalIdeal R) 0 := by
    rw [← Spec.map_comp]
    rfl
  let F : (thickObj R (maximalIdeal R) 0 G).left ⟶ ((Over.pullback (spMap (residue R))).obj G).left :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by rw [Category.assoc, hr]; exact pullback.condition)
  obtain ⟨Q₀, -⟩ := exists_tq_baseChange _ _ r E.X _ _ F ((isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G (thick R (maximalIdeal R) 0)).congr hr.symm (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)) Q₁
  exact ⟨Q₀⟩

end GlobalTheory.Raynaud

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEltInvDivAtSplitLab
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem heckeElt_inv_divAt_splitLab : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → k ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) k α → DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ :=
  fun V P e ϖ k α he hϖ hϖ2 hk hα => GlobalTheory.SplitHeckeLabel.divAt_inv V e P he ϖ hϖ hϖ2 k hk α hα

end GlobalTheory
end

