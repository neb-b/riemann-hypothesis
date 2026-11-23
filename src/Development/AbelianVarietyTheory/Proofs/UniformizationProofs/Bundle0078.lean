module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianDim

theorem exists_relDim_of_connected {S : Scheme.{0}} [ConnectedSpace S] (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) : ∃ g, SmoothOfRelativeDimension g B.hom := by
  have := hB.smooth
  have := hB.geomConnected
  have : ConnectedSpace B.left := (GroupConn.connectedSpace_group S B).1
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  exact exists_dim_of_preconnected B.hom x

theorem connectedSpace_spec_of_isLocalRing (A : Type) [CommRing A] [IsLocalRing A] :
    ConnectedSpace (Spec (CommRingCat.of A)) := by
  show ConnectedSpace (PrimeSpectrum A)
  rw [connectedSpace_iff_univ]
  refine ⟨⟨IsLocalRing.closedPoint A, trivial⟩, ?_⟩
  intro u v hu hv huv ⟨x, _, hx⟩ ⟨y, _, hy⟩
  have hc : IsLocalRing.closedPoint A ∈ u ∪ v := huv trivial
  rcases hc with h | h
  · exact ⟨y, trivial, (IsLocalRing.specializes_closedPoint y).mem_open hu h, hy⟩
  · exact ⟨x, trivial, hx, (IsLocalRing.specializes_closedPoint x).mem_open hv h⟩

theorem exists_relDim : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B], IsAbelianScheme B → ∃ g, SmoothOfRelativeDimension g B.hom := by
  intro A _ _ B _ hB
  have := connectedSpace_spec_of_isLocalRing A
  exact exists_relDim_of_connected B hB

end GlobalTheory.AbelianDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAddFinrankOfKernel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem dim_eq_add_finrank_of_kernel {S : Scheme.{0}} (y : S) {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G) [IsMonHom q]
    [IsMonHom i] [Flat q.left] [Surjective q.left] [IsAffineHom q.left] (hk : IsPullback i (toUnit _) q (η[B]))
    {g g' : ℕ} (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' B.hom) :
    g = g' + Module.finrank ℤ X := by
  have := (H1.torus_dim S X).smooth
  have : Smooth q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback i q hk).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (hk.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

theorem PreU.dim_eq : (AllPre fun {_} _ _ _ {D} {A} {_} _ _ _ => A.g = D.P.g + D.rank) := by
  intro V _ _ _ _ D A G _ _ U
  have hs : Smooth G.hom := U.semi.smooth
  have : GeometricallyConnected G.hom := U.semi.geomConnected
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group _ G).1
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have bc : ∀ {S' : Scheme.{0}} {X : Over (Spec (CommRingCat.of V))} {m : ℕ} (f : S' ⟶ Spec (CommRingCat.of V)),
      SmoothOfRelativeDimension m X.hom → SmoothOfRelativeDimension m ((Over.pullback f).obj X).hom :=
    fun f h => (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) h
  have h₁ : n = A.g := by
    have a := A.smoothDim
    have b : SmoothOfRelativeDimension (0 + A.g) ((Over.pullback (jK V)).obj G).hom := by
      have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
      rw [← Over.w U.gen.hom]; infer_instance
    exact (H1.dim_unique _ (bc _ hn) b (eSec _ (Classical.arbitrary (Spec (CommRingCat.of (FractionRing V)))))).trans (zero_add _)
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by simpa using (IsLocalRing.maximalIdeal.isMaximal V).ne_top)
  let c := U.gt 0
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  exact h₁.symm.trans (dim_eq_add_finrank_of_kernel (Classical.arbitrary _) c.q c.i c.isKernel (bc _ hn)
    (bc _ D.P.smoothDim))

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverField
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ExpTotal
open GlobalTheory.TwistLoc (gc gc_mul)

section General
variable {X X' W Y Z : Scheme.{0}}

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (scal p a) = gc (r ≫ p) z a := gs_pull r p z ⊤ trivial _

theorem gc_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (q : Z ⟶ Spec (CommRingCat.of S)) (z : Z) (a : R) :
    gc (q ≫ Spec.map (CommRingCat.ofHom f)) z a = gc q z (f a) := by
  refine (gs_pull q _ z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) ?_)
  exact (congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem exists_comb {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ} (c : Fin n → Γ(Y, ⊤))
    (t : Fin n → LB.Sec (LB.LinComb L φ ε)) : ∃ s : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s r z J = ∑ i, gs r z ⊤ (c i) * sval (t i) r z J :=
  ⟨⟨fun j => ∑ i, (IndivisibleSection.smulSec (c i) (t i)).f j, fun i j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (IndivisibleSection.smulSec (c l) (t l)).compat i j⟩,
    fun Z r z J hJ => DVR.SectionScalarValuation.sval_lin c t (fun _ => rfl) r z hJ⟩

theorem exists_inv {L : LB X} {L' : LB X'} {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) : ∃ v : LB.Iso (L.pull F) (L'.pull F'), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (i : L.ι) (j : L'.ι), F (r z) ∈ L.U i → F' (r z) ∈ L'.U j →
        gw v r z j (fun _ => i) = (gw w r z i (fun _ => j))⁻¹ := by
  let v : LB.Iso (L.pull F) (L'.pull F') := ⟨fun p => (res (le_inf inf_le_right inf_le_left :
    (L'.pull F').U p.1 ⊓ (L.pull F).U p.2 ≤ (L.pull F).U p.2 ⊓ (L'.pull F').U p.1) (w.s (p.2, p.1)))⁻¹⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (i : L.ι) (j : L'.ι), F (r z) ∈ L.U i → F' (r z) ∈ L'.U j →
      gw v r z j (fun _ => i) = (gw w r z i (fun _ => j))⁻¹ := fun Z r z i j hi hj =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _
      (show r z ∈ (L'.pull F').U (fun _ => j) ⊓ (L.pull F).U (fun _ => i) from ⟨mem_pull.2 hj, mem_pull.2 hi⟩) _))
  refine ⟨v, (isGen_iff v).2 fun Z r z j j' i i' hj hj' hi hi' => ?_, hv⟩
  have e := (isGen_iff w).1 hw Z r z (i PUnit.unit) (i' PUnit.unit) (fun _ => j) (fun _ => j') (mem_pull.1 hi)
    (mem_pull.1 hi') (mem_pull.2 hj) (mem_pull.2 hj')
  rw [gm_pull_g L' F' r z (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')] at e
  refine (hv Z r z (i PUnit.unit) j (mem_pull.1 hi) hj).trans ?_
  rw [e, gm_pull_g L F r z i i' hi hi']
  refine Eq.trans ?_ (congrArg _ (hv Z r z (i' PUnit.unit) j' (mem_pull.1 hi') hj')).symm
  rw [mul_inv, mul_inv, inv_inv, mul_comm _⁻¹]

end General

theorem exists_span (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ)
    (hn : 1 ≤ n) (F : Type) [Field F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
    (s : LB.Sec (LB.LinComb P.L (fun _ : Fin 1 => (snd (Over.mk q) P.A).left) (fun _ => (n : ℤ)))) :
    ∃ (m : ℕ) (c : Fin m → F) (a : Fin m → LB.Sec (LB.LinComb P.L (fun _ : Fin 1 => 𝟙 P.A.left) (fun _ => (n : ℤ)))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk q ⊗ P.A).left) (z : Z) (J), Good P.L z J →
        sval s r z J = ∑ i, gc (R := F) (r ≫ (fst (Over.mk q) P.A).left) z (c i) *
          sval (a i) (r ≫ (snd (Over.mk q) P.A).left) z J := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of K)) P n hn (IsLocalRing.closedPoint K)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  have hi : (Spec (CommRingCat.of K)).topIso.inv ≫
      (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom = 𝟙 _ :=
    (congrArg (_ ≫ ·) (Category.comp_id _)).trans (Spec (CommRingCat.of K)).topIso.inv_hom_id
  have hi' : (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom ≫ (Spec (CommRingCat.of K)).topIso.inv
      = 𝟙 _ :=
    (congrArg (· ≫ _) (Category.comp_id _)).trans (Spec (CommRingCat.of K)).topIso.hom_inv_id
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).left,
      t ≫ (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom = q :=
    ⟨q ≫ (Spec (CommRingCat.of K)).topIso.inv, (Category.assoc _ _ _).trans
      ((congrArg (q ≫ ·) hi).trans (Category.comp_id q))⟩
  let T₀ := overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤
  let e : P.A ⟶ T₀ ⊗ P.A := lift (Over.homMk (P.A.hom ≫ (Spec (CommRingCat.of K)).topIso.inv)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hi).trans (Category.comp_id _)))) (𝟙 _)
  have he : snd (baseAt t) P.A ≫ e = homAt t ▷ P.A := by
    refine CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext ?_) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (lift_snd _ _)).trans
      ((Category.comp_id _).trans (whiskerRight_snd (homAt t) P.A).symm)))
    have : IsIso T₀.hom := ⟨_, hi', hi⟩
    rw [← cancel_mono T₀.hom, Over.w, Over.w]
  choose a ha using fun i => PullSec.exists_pullSec P.isLB (φ' := fun _ : Fin 1 => 𝟙 P.A.left) e.left
    (fun _ => (congrArg CommaMorphism.left (lift_snd _ _ : e ≫ snd _ _ = _)).symm) (b i)
  choose b' hb' using fun i => IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
  have hsp := (hb F t b' fun i j => hb' i j _).2
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  choose c hc using fun i => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (d i)
  refine ⟨_, c, a, fun Z r z J hJ => ?_⟩
  refine (DVR.SectionScalarValuation.sval_lin (s := s) (fun i => scal (R := F) (fst (baseAt t) P.A).left (c i)) b' (fun j => ?_) r z hJ).trans
    (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (gs_scal _ r z _) ?_)
  · refine (congrFun (congrArg Subtype.val hd) j).symm.trans ?_
    refine (congrFun (Submodule.coe_sum _ _ _) j).trans ((Finset.sum_apply _ _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_))
    rw [← hc i]
    rfl
  · have e₁ : (r ≫ (snd (baseAt t) P.A).left) ≫ e.left = r ≫ (homAt t ▷ P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (congrArg CommaMorphism.left he))
    have e₂ : (r ≫ (homAt t ▷ P.A).left) ≫ (snd T₀ P.A).left = r ≫ (snd (baseAt t) P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)))
    refine Eq.trans ?_ (ha i Z _ z J hJ).symm
    rw [e₁, sval_of (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (b i) _ z J
      (fun _ => J (r ≫ (snd (baseAt t) P.A).left)) (fun _ => congrArg J e₂)]
    have hm := hJ.mem (fun _ : Fin 1 => (snd (baseAt t) P.A).left) r
    have le := chart_le_res P.A P.L (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) n
      (fun _ => J (r ≫ (snd (baseAt t) P.A).left))
    exact (congrArg (gs r z _) (hb' i _ le)).trans ((gs_res r z le hm _).trans (gs_pull r (homAt t ▷ P.A).left z _ (le hm) _))

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_integral (U : PreU I D A G) (k : ℕ)
    (a : LB.Sec (LB.LinComb A.L (fun _ : Fin 1 => 𝟙 A.A.left) (fun _ => (k : ℤ)))) :
    ∃ t : R, t ≠ 0 ∧ ∃ σ : U.SecGT (𝟙_ _) k, ∀ (Z : Scheme.{0}) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
      (rG : Z ⟶ (𝟙_ _ ⊗ G).left), rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) →
      ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
        sval σ rG z JG = gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z t *
          ((gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
            sval a (y ≫ U.gen.hom.left) z JA) := by
  have := U.semi.quasiCompact
  have := U.semi.separated
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  obtain ⟨v, hv, hvw⟩ := exists_inv U.wA U.wA_gen
  obtain ⟨s', hs'⟩ := PullSec.exists_sec_of_iso A.isLB U.P.L.isLB v hv (𝟙 _) U.gen.hom.left
    (pullback.fst G.hom (jK R) ≫ 𝟙 G.left) (𝟙 A.A.left) ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm) k a
  obtain ⟨t, ht, σ₀, hσ₀⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors R)
    (IsPullback.of_hasPullback G.hom (jK R)) U.P.L.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) s'
  obtain ⟨σ, hσ⟩ := PullSec.exists_pullSec U.P.L.isLB (φ' := fun _ : Fin 1 => (snd (𝟙_ _) G).left)
    (snd (𝟙_ _) G).left (fun _ => (Category.comp_id _).symm) σ₀
  refine ⟨t, nonZeroDivisors.ne_zero ht, σ, fun Z y rG e z JA JG hA hG => (hσ Z rG z JG hG).trans ?_⟩
  have mA := hA (y ≫ U.gen.hom.left)
  have mG := hG (y ≫ pullback.fst G.hom (jK R))
  rw [e, sval_of σ₀ _ z JG (fun _ => JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => congrArg JG (Category.comp_id _)),
    sval_of a _ z JA (fun _ => JA (y ≫ U.gen.hom.left)) (fun _ => congrArg JA (Category.comp_id _))]
  refine (hσ₀ Z y z _ (Set.mem_iInter.2 fun _ => mG)).trans (congrArg _ ?_)
  have h := hs' Z y z _ _ mA mG
  rw [Category.comp_id y, hvw Z y z _ _ mG mA] at h
  refine Eq.trans ?_ (congrArg _ h)
  rw [← _root_.mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow, _root_.one_mul]

theorem exists_pullB (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X)
    (f : SecBT D (𝟙_ _) k α) : ∃ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (rF : Z ⟶ (DegPre.BF D F).left) (rB : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
        rB ≫ (snd _ D.P.A).left = rF ≫ (DegPre.prB D F).left → ∀ (z : Z) (J), Good D.P.L z J →
          sval s rF z J = sval f rB z J := by
  let φ := toUnit (TF (R := R) F)
  have a₀ : snd (TF (R := R) F) D.P.A = φ ▷ D.P.A ≫ snd (𝟙_ _) D.P.A := (whiskerRight_snd _ _).symm
  have hc : ∀ i : Fin 4, DegPre.famφ D F α i = (φ ▷ D.P.A).left ≫ famφT D (𝟙_ _) α i := fun i => by
    have u : φ ▷ D.P.A ≫ toUnit (𝟙_ _ ⊗ D.P.A) = toUnit _ := toUnit_unique _ _
    have a₂ : ∀ c : 𝟙_ _ ⟶ D.P.A, toUnit (DegPre.BF D F) ≫ c = φ ▷ D.P.A ≫ toUnit (𝟙_ _ ⊗ D.P.A) ≫ c := fun c => by
      rw [← Category.assoc, u]
    fin_cases i
    · exact congrArg (fun q => q.left) a₀
    · exact congrArg (fun q => q.left) ((congrArg₂ (· * ·) a₀ (a₂ (D.c α))).trans (MonObj.comp_mul _ _ _).symm)
    · exact congrArg (fun q => q.left) (a₂ (D.c α))
    · exact congrArg (fun q => q.left) (a₂ η[D.P.A])
  obtain ⟨s, hs⟩ := PullSec.exists_pullSec D.P.isLB (φ ▷ D.P.A).left hc f
  refine ⟨s, fun Z rF rB e z J hJ => (hs Z rF z J hJ).trans (congrArg (sval f · z J) ?_)⟩
  have : IsIso (snd (𝟙_ _) D.P.A) := by rw [← leftUnitor_hom]; infer_instance
  have : IsIso (snd (𝟙_ _) D.P.A).left := inferInstanceAs (IsIso ((Over.forget _).map (snd (𝟙_ _) D.P.A)))
  rw [← cancel_mono (snd (𝟙_ _) D.P.A).left, e]
  exact (Category.assoc _ _ _).trans (congrArg (rF ≫ ·) (congrArg CommaMorphism.left a₀).symm)

theorem exists_expF (hS : SecBaseChangeSt) (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (k : ℕ) (hk : 1 ≤ k) (hb : ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f)
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) : ∃ s, U.ExpF F k t s := by
  obtain ⟨n, c, a, ha⟩ := exists_span hS A k hk F (jFK (R := R) F) t
  choose d hd σ hσ using fun i => exists_integral U k (a i)
  choose f hf using fun i => hb (σ i)
  choose g hg using fun i α => exists_pullB D F k α (f i α)
  let ψ : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hψ : ∀ i, ψ (d i) ≠ 0 := fun i => (map_ne_zero (algebraMap (FractionRing R) F)).2
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hd i))
  choose s hs using fun α => exists_comb
    (fun i => scal (R := F) (fst (TF (R := R) F) D.P.A).left (c i * (ψ (d i))⁻¹)) (fun i => g i α)
  refine ⟨s, n, fun i => c i * (ψ (d i))⁻¹, σ, f, hf, fun Z rA y rG e₁ e₂ z JA JG hA hG => ?_,
    fun α Z rF rB e z J hJ => (hs α Z rF z J hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg _ (hg i α Z rF rB e z J hJ))⟩
  refine (congrArg _ (ha Z rA z JA hA)).trans ((Finset.mul_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_))
  have e₃ : y ≫ pullback.fst G.hom (jK R) ≫ G.hom =
      ((rA ≫ (fst (TFK (R := R) F) A.A).left) ≫ jFK (R := R) F) ≫ jK R := by
    have w₁ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
    have w₂ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (congrArg (y ≫ ·) pullback.condition).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) ?_))
    exact (congrArg (y ≫ ·) w₁.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ A.A.hom) e₁.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (rA ≫ ·) w₂.symm).trans (Category.assoc _ _ _).symm))))
  have e₄ : gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z (d i) =
      gc (R := F) (rA ≫ (fst (TFK (R := R) F) A.A).left) z (ψ (d i)) :=
    (congrArg (gc · z (d i)) e₃).trans ((gc_map _ _ z _).trans (gc_map _ _ z _))
  refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_scal (R := F) _ rA z _) (hσ i Z y rG e₂ z JA JG hA hG)).symm
  rw [e₄, ← _root_.mul_assoc (gc _ _ _) (gc _ _ _), ← gc_mul, inv_mul_cancel_right₀ (hψ i)]
  exact (mul_left_comm _ _ _).trans (congrArg (fun q => _ * (_ * sval (a i) q z JA)) e₁)

theorem expF_total : Laws → Laws2 → (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ t, ∃ s, U.ExpF F k t s) :=
  fun h h₂ V _ _ _ hV D A G _ _ U F _ _ k hk t =>
    exists_expF h.secBaseChange U F k hk (_root_.GlobalTheory.BaseExpansionExists.main h h₂ V hV D A G U k hk) t

end GlobalTheory.UU.ExpTotal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenericFibreIsoOfModelIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT

theorem exists_genericFibre_iso_of_model_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G') (ψ : G' ≅ G), IsMonHom ψ.hom → LBIso U'.LG.L (U.LG.L.pull ψ.hom.left) → ∃ φ : A'.A ≅ A.A, IsMonHom φ.hom ∧ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom = U'.gen.hom ≫ φ.hom ∧ LBIso A'.L (A.L.pull φ.hom.left) := by
  intro R _ _ I D D' A A' G G' _ _ _ _ U U' ψ hψ hL
  have := U.gen_hom
  have := U'.gen_hom
  have := hψ
  have hm : ((Over.pullback (jK R)).map ψ.hom).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ ψ.hom.left :=
    pullback.lift_fst _ _ _
  have hi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  refine ⟨U'.gen.symm ≪≫ (Over.pullback (jK R)).mapIso ψ ≪≫ U.gen, ?_, by simp, ?_⟩
  · show IsMonHom (U'.gen.inv ≫ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom)
    infer_instance
  · have h₁ : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R))) :=
      LBIso.chartPull (chartPullSec A'.L _ U'.gen.inv.left hi)
        (chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK R)) _ U'.gen.inv.left fun _ => rfl) U'.ext
    have h₂ : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)))
        (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ ψ.hom.left)) :=
      LBIso.chartPull (chartPullPull U'.LG.L _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => ψ.hom.left) _ _ fun _ => rfl) hL
    have h₃ : LBIso (A.L.pull (U'.gen.symm ≪≫ (Over.pullback (jK R)).mapIso ψ ≪≫ U.gen).hom.left)
        (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ ψ.hom.left)) :=
      LBIso.chartPull (h := U'.gen.inv.left ≫ ((Over.pullback (jK R)).map ψ.hom).left)
        (chartPullSame A.L _ (fun _ => U.gen.hom.left) _ _ fun _ => (Category.assoc _ _ _).symm)
        (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ =>
          (Category.assoc _ _ _).trans ((congrArg (U'.gen.inv.left ≫ ·) hm.symm).trans (Category.assoc _ _ _).symm))
        U.ext
    exact LBIso.trans A'.isLB (pull_isLB U.LG.isLB _) (pull_isLB A.isLB _)
      (LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) h₁ h₂) h₃.symm

end GlobalTheory.UT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OLinearMatrixOfUnifPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PowMatrixLinear

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

theorem comp_prod {X Y M : C} [MonObj M] [IsCommMonObj M] {J : Type*} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ ∏ l ∈ s, g l = ∏ l ∈ s, f ≫ g l :=
  map_prod (MonoidHom.mk ⟨fun x : Y ⟶ M => f ≫ x, MonObj.comp_one f⟩
    (fun a b => MonObj.comp_mul f a b)) g s

theorem prod_comp {X M N : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N] {J : Type*}
    (s : Finset J) (g : J → (X ⟶ M)) (f : M ⟶ N) [IsMonHom f] :
    (∏ l ∈ s, g l) ≫ f = ∏ l ∈ s, g l ≫ f :=
  map_prod (IsMonHom.monoidHom f X) g s

end General

local instance splitTorus_isCommMonObj (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    IsCommMonObj (splitTorus S X) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj (splitTorusAff ZU X)))

end PowMatrixLinear


end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiMulPsiOfAdditionSecondVariableStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.psi_mul_psi_addition_second_variable : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (mu α : D.X), α = 0 → ∀ (c : F) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 2 α mu) (DegPre.deltaε 2))), (∀ i z J, Good D.P.L z J → sval (s' i (α + 2 • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D F c ⊤) * (sval (s' i α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val)) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → (val (Z := (TF (R := R) F).left) (D.psi (mu)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (-mu)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) mu).left z J).val = gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) * (val u (DegPre.zF D F).left z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J).val := by
  first | exact @GlobalTheory.psi_mul_psi_of_addition_second_variable | exact GlobalTheory.psi_mul_psi_of_addition_second_variable | (intros; apply GlobalTheory.psi_mul_psi_of_addition_second_variable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorPointZeroOfPowerEigenStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.thetaOperator_point_zero_of_power_eigen : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (l : ℕ), 1 ≤ l → ∀ (th : EA P p 1) (t : EA P p l) (θ : ThetaGrp P.A P.L (l : ℤ) (Over.mk p)) (c : Fˣ), th ≠ 0 → (∀ z J, Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((l : ℕ) : ℤ)) t.sec (𝟙 _) z J = sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th.sec (𝟙 _) z J ^ l) → IsActOf P.A P.L (l : ℤ) θ t.sec (c.val • t).sec → θ.pt = 1 := by
  first | exact @GlobalTheory.ThetaEigen.main | exact GlobalTheory.ThetaEigen.main | (intros; apply GlobalTheory.ThetaEigen.main <;> assumption)
end

