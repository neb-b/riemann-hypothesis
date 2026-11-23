module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0075
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.InfiniteTorsionOrCocharacterOfArcAtInfinity
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoMove
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullMove

theorem isThetaPt_iso {S : Scheme.{0}} {P P' : PolAV S} (φ : P.A ≅ P'.A) [IsMonHom φ.hom]
    (hw : LBIso P.L (P'.L.pull φ.hom.left)) {T : Over S} {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) :
    IsThetaPt P' k (fun i => x i ≫ φ.hom) v := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, Q⟩ := H.2.2 p
  refine ⟨V, hV, ?_⟩
  have hk' : ∀ i, (overResι V ≫ x i) ^ (k ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  have Q' := GlobalTheory.ThetaPtUp.isThetaPtOver_up (T := overRes V) (T₀ := overRes V) (𝟙 (overRes V).left)
    (Geo.Tor.isGrpPullback_of_iso φ) hw ((Category.id_comp _).trans (Category.comp_id _).symm)
    (x₀ := fun i => overResι V ≫ x i ≫ φ.hom)
    (fun i => (Category.id_comp _).trans (by rw [← Category.assoc]; rfl)) hk' Q
  rw [IsIso.inv_id] at Q'
  exact Q'

def tateMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop} (I : TateIso D k Q act e) (F : Q ≃* Q')
    (ha : ∀ c x, F (act c x) = act' c (F x))
    (he : ∀ n x y c, x ^ n = 1 → y ^ n = 1 → e n x y c → e' n (F x) (F y) c) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := F (I.ev n a)
  add n a b := by rw [I.add, map_mul]
  lin n c a := by rw [I.lin, ha]
  ker n hn a := by rw [F.map_eq_one_iff, I.ker n hn]
  onto n hn x := by
    obtain ⟨y, rfl⟩ := F.surjective x
    rw [← map_pow, F.map_eq_one_iff, I.onto n hn]
    exact exists_congr fun a => F.injective.eq_iff.symm
  tower n m hn hm a := by rw [← map_pow, I.tower n m hn hm]
  isom n hn a b := he n _ _ _ ((I.onto n hn _).2 ⟨a, rfl⟩) ((I.onto n hn _).2 ⟨b, rfl⟩) (I.isom n hn a b)

def ptEquiv {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A ≅ A') [IsMonHom φ.hom] (T : Over S) :
    (T ⟶ A) ≃* (T ⟶ A') where
  toFun x := x ≫ φ.hom
  invFun y := y ≫ φ.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := map_mul (IsMonHom.monoidHom φ.hom T)

theorem exists_tateIso_move : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (φ : o.P.A ≅ o'.P.A), IsPolIso o.P o'.P φ → (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) → ∃ I' : (letI := H.starRing; TateIso D K (baseOver (Sp K) ⟶ o'.P.A) (fun a g => g ≫ o'.oa.act a) (fun n g g' c => WeilIs o'.P.A o'.P.L n g g' (unitOn c))), I'.ζ = o.I.ζ ∧ (∀ M a, I'.ev M a = o.I.ev M a ≫ φ.hom) ∧ ∀ m v, o.Theta m v → Full.Theta { o' with I := I' } m v := by
  intro hL E _ _ _ H D K _ _ o o' φ ⟨hφ, t⟩ hact
  letI := H.starRing
  obtain ⟨w, hw⟩ := LBIso.symm t
  refine ⟨tateMap o.I (ptEquiv φ _) (fun c x => ?_) (fun n x y c hx hy h => ?_), rfl, fun _ _ => rfl, fun m v h => ?_⟩
  · show (x ≫ o.oa.act c) ≫ φ.hom = (x ≫ φ.hom) ≫ o'.oa.act c
    rw [Category.assoc, hact, Category.assoc]
  · exact (weilIs_iso_iff hL.globalFns hL.cube o.P o'.P φ w hw n x y hx hy _).2 h
  · exact isThetaPt_iso φ ⟨w, hw⟩ (fun a => (o.I.onto _ (pow_pos h.1.pos 2) _).2 ⟨a, rfl⟩) h

end GlobalTheory.FullMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPullbackNonzeroOnClosedFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ThetaFibre

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem proj_mulVec_mem (hB : BaseFacts S M U₀ EE) (z : M.Z) {v : S.J → Ω} (hv : v ∈ EE.E z) :
    ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v ∈ EE.E z := by
  have hT : S.TT M z ≤ S.HH M z := (hB.free z).2 ▸ (hB.free z).1.1
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have := Fintype.ofFinite (S.TT M z)
  have e : ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v =
      algebraMap o (M.O z) (Ring.inverse (Nat.card (S.TT M z) : o)) •
        ∑ t : S.TT M z, ((S.ρ t).map (algebraMap o Ω)).mulVec v := by
    ext i
    simp [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.mulVec, dotProduct, Matrix.sum_apply,
      Algebra.smul_def (A := Ω), Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => hB.stab z _ (hT t.2) v hv)

theorem proj_mulVec_regular (hB : BaseFacts S M U₀ EE) {z : M.Z} (hz : IsClosed ({z} : Set M.Z))
    {v : S.J → Ω} (hv : v ∈ EE.E z) (j : S.J) :
    ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v j ∈ M.O z := by
  refine hB.zero z hz _ (proj_mulVec_mem hB z hv) ?_ j
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
    GlobalTheory.ThetaBound.proj_mul_proj S _ _ le_rfl (hB.free z).1.1 (hB.free z).1 0 0 fun _ => rfl]

theorem proj_col_eq_zero (hB : BaseFacts S M U₀ EE) {z : M.Z} (hz : IsClosed ({z} : Set M.Z))
    {K : Type} [Field K] (y : M.O z →+* K) (B : Matrix S.J S.J Ω) (hBm : ∀ k, B k ∈ EE.E z)
    (a : S.J → M.O z) (i : S.J) (ha : ∀ j, ∑ k, (a k : Ω) * B k j = (1 : Matrix S.J S.J Ω) i j)
    (h0 : ∀ k, y (a k) = 0) (j : S.J) :
    y (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) = 0 := by
  have e : algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i) =
      ∑ k, a k * ⟨_, proj_mulVec_regular hB hz (hBm k) j⟩ := by
    apply Subtype.ext
    have h1 : ∑ m, algebraMap o Ω (S.proj (S.TT M z) 0 j m) * (1 : Matrix S.J S.J Ω) i m =
        algebraMap o Ω (S.proj (S.TT M z) 0 j i) := by
      simp [Matrix.one_apply]
    simp only [Subalgebra.coe_algebraMap, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
    rw [← h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  exact Finset.sum_eq_zero fun k _ => by rw [map_mul, h0, zero_mul]

theorem exists_mem_nonzeroLocus_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ x ∈ nonzeroLocus (Q.st ρ.i₀), x ∈ Q.G ∧ Q.P.hom x = z := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q hbig hgeo z hz
  by_contra hne
  have hzc : z ∈ ⨆ l, Q.W l := by rw [Q.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hzc
  obtain ⟨K, _, x, hx, hind⟩ := _root_.GlobalTheory.ZH.IndepFib.indep_on_closed_fibre hL o Ω S ρ M U₀ EE hB Q hbig hgeo l z hl hz
  have hc : (fun k => valF x (Q.W l) (Q.c l ρ.i₀ k)) = 0 := by
    refine hind _ fun g j hg hgx => ?_
    by_cases hj : ⊤ ≤ g ⁻¹ᵁ (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι).U j
    · have hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) g
          (fun i => valF g _ ((Q.σ l i).f j)) :=
        ⟨j, 1, hj, fun i => by rw [Units.val_one, _root_.one_mul]; rfl⟩
      have hr := Q.rel l K g _ hw
      rw [hgx] at hr
      by_contra h0
      have hu := (CrdCalc.crd_isUnit_iff ρ.i₀ hr).1 (isUnit_iff_ne_zero.2 h0)
      refine hne ⟨(g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (IsLocalRing.closedPoint K), hu (Set.mem_univ _),
        hg ⟨_, rfl⟩, ?_⟩
      have hm : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rw [hx] at hm
      rw [← hgx] at hm
      exact hm
    · exact Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (dif_neg hj)
  obtain ⟨j, hj⟩ := GlobalTheory.proj_zero_pullback_ne_zero hL o Ω S ρ K
    ((RatModel.valHom x z hx).comp (algebraMap o (M.O z))) _ (hB.free z).1
  refine hj (proj_col_eq_zero hB hz (RatModel.valHom x z hx) (Q.B l)
    (fun k => by rw [Q.basis l z hl]; exact Submodule.subset_span ⟨k, rfl⟩)
    (fun k => ⟨_, RatModel.valF_mem_O hl (Q.c l ρ.i₀ k)⟩) ρ.i₀
    (fun j => congrFun (congrFun (Q.c_inv l) ρ.i₀) j) (fun k => ?_) j)
  rw [RatModel.valHom_apply, RatModel.val_valF (by rw [hx]; exact Set.singleton_subset_iff.2 hl)]
  exact congrFun hc k

end GlobalTheory.ZH.ThetaFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusAbelianQuotientPDivisibleSmoothGroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.DivSemi

theorem smooth_proj {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G B : Over S} [GrpObj G] [GrpObj B] {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsQuot i q) : Smooth q.left := by
  obtain ⟨hi, hq, hf, hs, ha, hk, -⟩ := h
  have := (H1.torus_dim S X).smooth
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((H1.torsor_pullback i q hk).map (Over.forget _)).flip
    ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
  exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this

theorem dim_eq_add {S : Scheme.{0}} (y : S) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G B : Over S} [GrpObj G] [GrpObj B] {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsQuot i q) {g g' : ℕ}
    (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' B.hom) :
    g = g' + Module.finrank ℤ X := by
  have := smooth_proj h
  obtain ⟨hi, hq, hf, hs, ha, hk, -⟩ := h
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (hk.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

theorem exists_lift_point {k : Type} [Field k] [IsAlgClosed k] {G B : Over (Sp k)} (q : G ⟶ B)
    [LocallyOfFiniteType q.left] [QuasiCompact q.left] [Surjective q.left] (y : 𝟙_ (Over (Sp k)) ⟶ B) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ G, x ≫ q = y := by
  let x : Sp k ⟶ B.left := y.left
  have : CompactSpace ↥(pullback q.left x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q.left x)
  obtain ⟨p, -⟩ := (pullback.snd q.left x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback q.left x)) ⟨p, trivial⟩
  have e : (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ≫ q.left = x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ?_, ?_⟩
  · rw [← Over.w q, ← Category.assoc]
    exact (congrArg (· ≫ B.hom) e).trans (Over.w y)
  · exact Over.OverMorphism.ext e

theorem isMonHom_id_pow {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (n : ℕ) :
    IsMonHom ((𝟙 B) ^ n : B ⟶ B) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 B) ^ n) (𝟙 B) ≫ μ[B]))

theorem exists_torus_abelian_quotient :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], SmConn G → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ^ p = y) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ IsAbelianScheme B ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ a, SmoothOfRelativeDimension a B.hom ∧ g = a + Module.finrank ℤ X := by
  intro k _ _ p _ _ G _ hG hp
  obtain ⟨X, _, _, _, B, _, i, q, hQ, hmax⟩ := _root_.GlobalTheory.SS.MaxTorus.exists_quot_no_cocharacter k G hG
  have hsm := smooth_proj hQ
  have hQ' := hQ
  obtain ⟨hi, hq, hf, hs, ha, hk, hB⟩ := hQ'
  have hB' := hB
  obtain ⟨hc, h₁, h₂, h₃, h₄⟩ := hB'
  have hgi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom h₁ h₄
  have hint : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hfin : Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ p = 1} := by
    have e : ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ≫ ((𝟙 B) ^ p : B ⟶ B) = x ^ p := fun x => by
      rw [MonObj.comp_pow, Category.comp_id]
    have := GlobalTheory.SS.finite_ker_of_surjective_points k B hB ((𝟙 B) ^ p) (isMonHom_id_pow B p) fun y => by
      obtain ⟨y', rfl⟩ := exists_lift_point q y
      obtain ⟨x, rfl⟩ := hp y'
      exact ⟨x ≫ q, by rw [e, MonObj.pow_comp]⟩
    simpa only [e] using this
  have hpr : IsProper B.hom := by
    refine _root_.GlobalTheory.ArcProper.isProper_of_arcs k B h₂ inferInstance h₃ fun a ha => ?_
    by_contra hn
    rcases _root_.GlobalTheory.SS.infinite_torsion_or_cocharacter k p B hB a ha hn with h | ⟨f, hf, hf'⟩
    · exact not_finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ p = 1}
    · exact hf' (hmax f hf)
  refine ⟨X, _, ‹_›, ‹_›, B, _, i, q, hQ, ⟨hc, h₁, hpr, h₄⟩, fun g hg => ?_⟩
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  obtain ⟨a, ha⟩ := exists_dim_of_preconnected B.hom x
  exact ⟨a, ha, dim_eq_add (default : PrimeSpectrum k) hQ hg ha⟩

end GlobalTheory.SS.DivSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTestOfGeometricTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem Clos.exists_core_test_of_geoTest : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∃ (τ : ex.core.Test y) (e : pullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j) ≅ t.mod.Φ.G.left), e.hom ≫ t.mod.Φ.G.hom = pullback.snd _ _ ∧ e.hom ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex p _ y y₀ t c tm hbig
  have hin := _root_.GlobalTheory.ZH.TestInOpen.top_le_preimage_G hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig
  have hrange : Set.range (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⊆ Set.range Q.G.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hin (Set.mem_univ x)
  let f' : t.u.G.left ⟶ Q.G.toScheme := IsOpenImmersion.lift Q.G.ι _ hrange
  have hf' : f' ≫ Q.G.ι = tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨-, hloc, hinj, -⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ t.u
  obtain ⟨-, -, hsm, -, hsplit⟩ := _root_.GlobalTheory.ZH.utest_dim_and_split hL o Ω S ρ p y₀ t.u
  have hgen := t.u.U.gen_hom
  have g1 : IsGrpPullback ((Over.pullback (jK t.u.V)).obj t.u.G) ρ.P.A (c.yK ≫ Q.u₀)
      (tm.φ ≫ pullback.fst ρ.P.A.hom Q.u₀) :=
    ((isGrpPullback_of_iso t.u.U.gen).comp t.u.cart).congr
      ((Category.id_comp _).trans c.yK_u.symm) tm.φ_fst.symm
  have g2 : IsGrpPullback ((Over.pullback (jK t.u.V)).obj t.u.G) ((Over.pullback Q.u₀).obj ρ.P.A) c.yK tm.φ :=
    (isGrpPullback_pullback ρ.P.A Q.u₀).cancel g1 tm.φ_snd
  let τ : ex.core.Test y :=
    { V := t.u.V
      complete := t.u.complete
      j := t.u.j
      j_inj := hinj
      j_loc := hloc
      y₀ := c.yV
      fac := c.fac
      H := t.u.G
      smooth := hsm
      sep := t.u.U.separated
      qc := t.u.semi.quasiCompact
      split := hsplit
      f := f'
      f_over := by
        change f' ≫ Q.G.ι ≫ Q.P.hom = _
        rw [← Category.assoc, hf', Category.assoc]
        exact tm.f_over
      yK := c.yK
      yK_fac := c.yK_fac
      φ := tm.φ
      φ_cart := g2
      φ_f := by
        change tm.φ ≫ ex.a = pullback.fst t.u.G.hom (jK t.u.V) ≫ f'
        rw [← cancel_mono Q.G.ι, Category.assoc, ex.a_eq, Category.assoc, hf']
        exact tm.φ_f
      imm := _root_.GlobalTheory.ZH.FibreImm.isClosedImmersion_special_fibre hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig f' hf'
      lift := by
        intro b hb
        change Sp (OO p) ⟶ Q.G.toScheme at b
        obtain ⟨c', h1, h2⟩ := _root_.GlobalTheory.ZH.ClosLift.exists_lift hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig (b ≫ Q.G.ι)
          ((Category.assoc _ _ _).trans hb) (by
            intro x _
            change (b ≫ Q.G.ι) x ∈ Q.G
            rw [Scheme.Hom.comp_apply]
            exact (b x).2)
        refine ⟨c', h1, ?_⟩
        change c' ≫ f' = b
        rw [← cancel_mono Q.G.ι, Category.assoc, hf']
        exact h2 }
  have hc : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  refine ⟨τ, hc.isoPullback.symm, hc.isoPullback_inv_snd, ?_⟩
  change hc.isoPullback.inv ≫ _ = pullback.fst t.u.G.hom (rPt p ≫ spMap t.u.j) ≫ f' ≫ Q.G.ι
  rw [hf', ← Category.assoc, hc.isoPullback_inv_fst]

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.CubeRootAut

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem cubeCls_pair {T : Over S} (x y : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y] c = pull (x * y).left c - pull x.left c - pull y.left c + pull (1 : T ⟶ G).left c := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![x, y] I).left c) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, p₀, p₁, p₂, p₄]
  have c₁ : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [c₁, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

theorem cubeCls_triple {T : Over S} (x y z : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y, z] c = pull (x * y * z).left c - pull (x * y).left c - pull (x * z).left c -
      pull (y * z).left c + pull x.left c + pull y.left c + pull z.left c - pull (1 : T ⟶ G).left c := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 3)) ≃ Finset (Fin 3)) _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (psum G ![x, y, z] I).left c) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have p₀ : psum G ![x, y, z] ∅ = 1 := rfl
  have p₁ : psum G ![x, y, z] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y, z] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y, z] {2} = z := _root_.mul_one z
  have p₄ : psum G ![x, y, z] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₅ : psum G ![x, y, z] {0, 2} = x * z := congrArg (x * ·) (_root_.mul_one z)
  have p₆ : psum G ![x, y, z] {1, 2} = y * z := congrArg (y * ·) (_root_.mul_one z)
  have p₇ : psum G ![x, y, z] {0, 1, 2} = x * y * z :=
    (congrArg (fun w => x * (y * w)) (_root_.mul_one z)).trans (_root_.mul_assoc x y z).symm
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇]
  have c₁ : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c₂ : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₃ : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₄ : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  simp only [c₁, c₂, c₃, c₄, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

end General

end GlobalTheory.ZH.CubeRootAut
end
end

