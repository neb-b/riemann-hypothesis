module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0818
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
section
noncomputable section

open Module NumberField
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.OneForm

section GroupAlgebra

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]


open Classical in
def typeSum (P : Subgroup G) (ψ : P →* Kˣ) (χ : G → K) : K := ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K)

end GroupAlgebra

section Modules

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V]

omit [CharZero K] in
theorem asAlg_eq_sum (r : Representation K G V) (a : MonoidAlgebra K G) (x : V) :
    r.asAlgebraHom a x = ∑ g : G, a.coeff g • r g x := by
  conv_lhs => rw [eq_sum_single a]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, LinearMap.sum_apply]



end Modules

section Coordinates

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem range_toF {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G)
    (Z : Submodule K B.S.Forms) :
    LinearMap.range (B.toF ℓ Z) = Z ⊓ LinearMap.range (B.r.asAlgebraHom (goodAt ℓ.X ℓ.P ℓ.ψ)) := by
  have hop : ∀ (a : MonoidAlgebra K G) (φ : B.S.Forms), B.S.gaOp B.r a φ = B.r.asAlgebraHom a φ := by
    intro a φ
    rw [asAlg_eq_sum, CSD.gaOp, LinearMap.sum_apply]
    rfl
  have hV : LinearMap.range (B.vE ℓ).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
  ext φ
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(B.mem_goodPart_iff ℓ Z _).1 (B.zE_mem ℓ Z y), ?_⟩
    have : (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y) ∈ LinearMap.range (B.vE ℓ).mulVecLin := ⟨_, rfl⟩
    rw [hV] at this
    obtain ⟨u, hu⟩ := this
    refine ⟨B.S.basis.equivFun.symm u, ?_⟩
    rw [B.toF_apply, ← hu, ← hop, LinearEquiv.eq_symm_apply, ← CSD.gaMat_mulVec_equivFun,
      LinearEquiv.apply_symm_apply]
    rfl
  · rintro ⟨hZ, w, hw⟩
    have : B.S.basis.equivFun φ ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
      rw [hV]
      refine ⟨B.S.basis.equivFun w, ?_⟩
      rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun, hop, hw]
    obtain ⟨u, hu⟩ := this
    rw [Matrix.mulVecLin_apply] at hu
    have hu0 : u ∈ B.Z0 ℓ Z := by
      rw [BlockDat.Z0, B.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
      exact hZ
    obtain ⟨y, hy⟩ := B.exists_zE ℓ Z hu0
    exact ⟨y, by rw [B.toF_apply, hy, hu, LinearEquiv.symm_apply_apply]⟩

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem iC_cpt (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  classical
  conv_rhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CxData.iC, lin_apply, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (x k) : Fin _ → K) = x k • Pi.single k 1 := by
    funext i; by_cases hi : i = k <;> simp [hi]
  rw [this, map_smul, map_smulₛₗ, map_smul]
  rfl

end Coordinates

section Family

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  {A : FamIn K G Pl0 T m}

def OneVector (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ χ ∈ X, typeSum P ψ χ = (Nat.card P : K)

section Faces

variable (X : CxData A.fam.amb) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

end Faces

end Family

section Concrete

open Formalism.BasicNotions Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def rowSub (R : RealDat D A Ks) (t : T) : Submodule D.what₂.LL (A.fam.amb.FR t) :=
  (LinearMap.range (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A.v0) (R.Th t)))).comap
    (Tw.semi (σ' := A.v0.embedding) (twAt D.what₂.embLL A.v0) R.emb0 (R.jX t))

def GoodInduced (R : RealDat D A Ks) : Prop :=
  ∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar R.Pg D.R.r D.what₂.embLL fun g => χ (R.eG.symm g)

theorem oneVector_of_whittaker (R : RealDat D A Ks) (F : Face D A) (hW : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector)
    (hlev : R.grp_levels F) (hind : GoodInduced R) : OneVector A.X F.P0 F.ψ0 := by
  classical
  obtain ⟨ψ, hψ, hP, -⟩ := hlev
  intro χ hχ
  have h := hW D.host.E R.Pg D.R.r ℂ (RingHom.id ℂ) ψ hψ (fun g => D.what₂.embLL (χ (R.eG.symm g))) (hind χ hχ)
  rw [← hP] at h
  let e : (R.levR F false).H ≃ F.P0 := R.eG.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl
  apply D.what₂.embLL.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_natCast, ← Nat.card_congr e, ← h, typeSum, map_sum]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum
  letI := GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH (R.levR F false)
  refine (Fintype.sum_equiv e _ _ fun x => ?_).symm
  rw [map_mul]
  rfl

end Concrete

end GlobalTheory.OneForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemeDvrSectionsMulEquivGeneric
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
namespace GlobalTheory.LevExt

noncomputable def pullPtsEquiv {S S' : Scheme.{0}} (A : Over S') [GrpObj A] (G : Over S) [GrpObj G] (f : S' ⟶ S)
    (φ : A.left ⟶ G.left) (h : IsGrpPullback A G f φ) (T : Over S') :
    (T ⟶ A) ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.mk' (Equiv.ofBijective
    (fun x => Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w]))
    (by
      constructor
      · intro x x' hx
        have hx' : x.left ≫ φ = x'.left ≫ φ := congrArg CommaMorphism.left hx
        ext1
        exact h.1.hom_ext hx' (by rw [Over.w, Over.w])
      · intro z
        refine ⟨Over.homMk (h.1.lift z.left T.hom (by simpa using z.w)) (by simp), ?_⟩
        ext1
        exact h.1.lift_fst _ _ _))
    (by
      intro x y
      ext1
      exact (h.2 T x y (Over.homMk (x.left ≫ φ) (by
          simp only [Over.mk_hom, Category.assoc]
          rw [h.1.w, ← Category.assoc, Over.w])) (Over.homMk (y.left ≫ φ) (by
          simp only [Over.mk_hom, Category.assoc]
          rw [h.1.w, ← Category.assoc, Over.w])) rfl rfl).symm)

noncomputable def precompEquiv {C : Type*} [Category C] [CartesianMonoidalCategory C] {T₁ T₂ M : C} [GrpObj M]
    (i : T₁ ≅ T₂) : (T₂ ⟶ M) ≃* (T₁ ⟶ M) where
  toFun x := i.hom ≫ x
  invFun x := i.inv ≫ x
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := MonObj.comp_mul _ _ _

end GlobalTheory.LevExt

namespace GlobalTheory.LevExt

theorem sections_generic_mulEquiv : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper G.hom → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∃ e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G), ∀ y, y.left ≫ φ = spMap (algebraMap W L) ≫ (e y).left := by
  intro W L _ _ _ _ _ _ G _ A _ φ hP hφ
  obtain ⟨e1, he1⟩ := _root_.GlobalTheory.ValPts.points_generic_mulEquiv W L (Sp W) G hP (𝟙 (Sp W))
  let i : Over.mk (spMap (algebraMap W L) ≫ 𝟙 (Sp W)) ≅ Over.mk ((𝟙_ (Over (Sp L))).hom ≫ spMap (algebraMap W L)) :=
    Over.isoMk (Iso.refl _) (by simp)
  let e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G) :=
    ((pullPtsEquiv A G (spMap (algebraMap W L)) φ hφ _).trans (precompEquiv i)).trans e1.symm
  refine ⟨e, fun y => ?_⟩
  have h1 := he1 (e y)
  have h2 : e1 (e y) = i.hom ≫ pullPtsEquiv A G (spMap (algebraMap W L)) φ hφ _ y := e1.apply_symm_apply _
  rw [h2] at h1
  simp only [i] at h1
  simp only [Over.isoMk_hom_left, Iso.refl_hom, Over.comp_left] at h1
  rw [← h1]
  simp only [Category.id_comp]
  rfl

end GlobalTheory.LevExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
section
namespace GlobalTheory.ScalarPoin

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def laS (X : Data E r) (k : ℕ) : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then (k : ℤ) else -(k : ℤ)

def qS (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x : Frame X.Ψ r) : ℂ :=
  ∏ τ, ((KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) ^ k

theorem qS_pow (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x : Frame X.Ψ r) :
    qS X x0 k x = qS X x0 1 x ^ k := by
  simp only [qS, pow_one, Finset.prod_pow]

theorem qS_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)) :
    qS X x0 k (cpt X x0 z) = 1 := by
  unfold qS
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [KU.Mx_cpt X ho, KU.tl_nM₂₂, ExF.det_unipotentFrame_eq_one, KU.tl, Matrix.det_submatrix_equiv_self, ExF.det_nM]
  simp

end

end GlobalTheory.ScalarPoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalVectorMemIdealCompletedLatticeIff
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdealCap

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem closure_eq_hat (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 E)) :
    AddSubgroup.closure {u : Fin n → GlobalTheory.AdLat.RA F E | ∃ b ∈ I, ∃ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      u = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i} =
      GlobalTheory.AdLat.hat F ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨b, hb, z, hz, rfl⟩
    rw [SetLike.mem_coe]
    induction hz using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨a, ha, b • x, Submodule.smul_mem_smul hb hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
    | zero =>
      convert AddSubgroup.zero_mem _ using 1
      funext i; simp
    | add w w' _ _ h h' =>
      convert add_mem h h' using 1
      funext i; simp [mul_add]
    | neg w _ h =>
      convert neg_mem h using 1
      funext i; simp
  · unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx ⊢
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro b hb y hy
      refine AddSubgroup.subset_closure ⟨b, hb, fun i => a ⊗ₜ y i,
        AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
    · intro y y' h h'
      convert add_mem h h' using 1
      funext i; simp [TensorProduct.tmul_add]

theorem span_smul_eq_top (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span E ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro x hx
  have hb1 : algebraMap (𝓞 E) E b ≠ 0 := by
    simpa using hb0
  have e : x = (algebraMap (𝓞 E) E b)⁻¹ • (b • x) := by
    rw [← algebraMap_smul E b x, smul_smul, inv_mul_cancel₀ hb1, one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.smul_mem_smul hb hx))

end General

theorem finVec_mem_closure_iff : ∀ (D : D7) (V : HSp D) (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ a : Fin V.rank → D.host.E, finVec V a ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} ↔ a ∈ I • latG V 1 := by
  intro D V I hI a
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hfg' : (I • latG V 1).FG := Submodule.FG.smul (IsNoetherian.noetherian I) hfg
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg'
    (span_smul_eq_top _ I hI hsp)).1 a
  rw [hhat, ← key, ← closure_eq_hat]
  rfl

end GlobalTheory.IdealCap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResInjOfDetermined
section
noncomputable section

namespace GlobalTheory.LowTypeRestriction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DeterminedByLowTypes : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ →
    (∀ τ, lowT M τ ≠ ⊥) → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ,
      (∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) → T = 0

theorem resInj_of_determined (h : DeterminedByLowTypes) : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj :=
  fun D _ _ _ _ _ _ _ _ _ _ R hθ i U hU hv =>
    h D _ _ (R.MW i _) R.θ hθ (lowT_ne_bot _) _ _ U hU hv

end GlobalTheory.LowTypeRestriction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResSConjGen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResConjPlace

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_mem_int (τ : E →ₐ[F] E) {s : E ⊗[F] Formalism.L2.Herm.Af F} (hs : s ∈ Formalism.L2.Herm.intAf F E) :
    Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) s ∈ Formalism.L2.Herm.intAf F E := by
  have : Formalism.L2.Herm.intAf F E ≤ (Formalism.L2.Herm.intAf F E).comap (Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩)
    · obtain ⟨c', hc'⟩ : ∃ y' : 𝓞 E, (y' : E) = τ (c : E) :=
        ⟨⟨τ (c : E), (c.isIntegral_coe).map ((τ : E →+* E).toIntAlgHom)⟩, rfl⟩
      refine Subring.subset_closure (Or.inl ⟨⟨_, c', rfl⟩, ?_⟩)
      show (c' : E) ⊗ₜ[F] _ = τ (c : E) ⊗ₜ[F] _
      rw [hc']; rfl
    · refine Subring.subset_closure (Or.inr ⟨b, ?_⟩)
      show _ = τ 1 ⊗ₜ[F] _
      rw [map_one]; rfl
  exact this hs

end General

end GlobalTheory.ResConjPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionAdjointOfAdjointOnSpanningFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AdjSpan

open GlobalTheory.CechPic

theorem adj_of_span : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ∀ (act : O → (A ⟶ A)), IsRAct A act → (∀ i, LBIso (Q.pull (lift (fst A A ≫ act (e i)) (snd A A)).left) (Q.pull (lift (fst A A) (snd A A ≫ act (bar (e i)))).left)) → Adj A Q bar act := by
  intro S A _ _ Q hQ O _ bar r e hbar hspan act hact he
  obtain ⟨hA, hL, h₁, h₂, -, hamp⟩ := hQ
  have hbi := GlobalTheory.Biadditive.biadditive_of_triv_axes GlobalTheory.globalFns_holds S A _ hA (pull_isLB hL _) hamp Q hL h₁ h₂

  letI : Add (Pic (A ⊗ A).left) := (inferInstance : AddCommGroup (Pic (A ⊗ A).left)).toAdd
  let B : ((A ⊗ A) ⟶ A) → ((A ⊗ A) ⟶ A) → Pic (A ⊗ A).left := fun u v => pull (lift u v).left (cls Q hL)
  have addL : ∀ u u' v, B (u * u') v = B u v + B u' v := fun u u' v => by
    have z := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 (hbi (A ⊗ A) u u' v).1
    rw [cls_linComb hL, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    show pull _ _ = pull _ _ + pull _ _
    rw [← sub_eq_zero, ← z]
    abel
  have addR : ∀ u v v', B u (v * v') = B u v + B u v' := fun u v v' => by
    have z := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 (hbi (A ⊗ A) v v' u).2
    rw [cls_linComb hL, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    show pull _ _ = pull _ _ + pull _ _
    rw [← sub_eq_zero, ← z]
    abel
  let f : O → Pic (A ⊗ A).left := fun a => B (fst A A ≫ act a) (snd A A) - B (fst A A) (snd A A ≫ act (bar a))
  have fadd : ∀ a b, f (a + b) = f a + f b := fun a b => by
    simp only [f]
    rw [hbar, hact.2.2.2, hact.2.2.2, MonObj.comp_mul, MonObj.comp_mul, addL, addR]
    abel
  let F : O →+ Pic (A ⊗ A).left := AddMonoidHom.mk' f fadd
  have Fe : ∀ i, F (e i) = 0 := fun i => by
    show f (e i) = 0
    exact sub_eq_zero.2 ((cls_eq_iff (pull_isLB hL _) (pull_isLB hL _)).2 (he i))
  have hker : Submodule.span ℤ (Set.range e) ≤ LinearMap.ker F.toIntLinearMap :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Fe i)
  intro a
  have ha : F a = 0 := hker (hspan ▸ Submodule.mem_top : a ∈ Submodule.span ℤ (Set.range e))
  exact (cls_eq_iff (pull_isLB hL _) (pull_isLB hL _)).1 (sub_eq_zero.1 ha)

end GlobalTheory.AdjSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDegreeTwoClassDiesOnPrincipalOpStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (exact GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen <;> assumption)
end

