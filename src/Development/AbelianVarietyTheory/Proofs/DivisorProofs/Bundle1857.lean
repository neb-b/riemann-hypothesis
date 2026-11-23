module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorsEqAtRealPlacesSameExponents
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulEqOfHatCNeZeroOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfRhoEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTwoTriplesAgree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealMapsChars

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem acts_of_eqOn {κ : Type} [Fintype κ] {T T' : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (hT : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ = T' Φ) {φ φ₁ : (κ → mixedEmbedding.mixedSpace F) → ℂ}
    (h : Acts (evI F) T φ φ₁) : Acts (evI F) T' φ φ₁ := by
  intro r hr
  rw [← hT _ hr.2]
  exact h r hr

theorem actsD_of_eqOn {κ : Type} [Fintype κ] {T T' : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (hT : ∀ t, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T t Φ = T' t Φ) {φ φ₁ : (κ → mixedEmbedding.mixedSpace F) → ℂ}
    (h : ActsD (evI F) T φ φ₁) : ActsD (evI F) T' φ φ₁ := by
  intro r hr x
  have : (fun t => T' t (tens (evI F) φ r) x) = fun t => T t (tens (evI F) φ r) x := by
    funext t; rw [hT t _ hr.2]
  rw [this]
  exact h r hr x

theorem one_mem_uAt {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {X : Spc F E n} : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
  intro u _
  simp [mat]

end GlobalTheory.RealMapsChars


open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealMapsChars in
theorem GlobalTheory.RealMapsChars.isRealMaps_of_sameExp : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  intro hP F E _ _ _ _ _ σ B a a' Γ Xa Xb oa oa' ob ob' R hA hB hR
  obtain ⟨hV, hV'⟩ := _root_.GlobalTheory.ArchWeil.weil_eq_at_real_places F E σ B a a' Γ Xa Xb oa oa' ob ob' hA hB
  have lV : ∀ g ∈ UAt σ Γ.V (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (g, 1) Φ = ob (g, 1) Φ :=
    fun g hg Φ hΦ => hV g 1 hg one_mem_uAt Φ hΦ
  have lV' : ∀ g ∈ UAt σ Γ.V' (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (g, 1) Φ = ob' (g, 1) Φ :=
    fun g hg Φ hΦ => hV' g 1 hg one_mem_uAt Φ hΦ
  have lW : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (1, h) Φ = ob (1, h) Φ :=
    fun h hh Φ hΦ => hV 1 h one_mem_uAt hh Φ hΦ
  have lW' : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (1, h) Φ = ob' (1, h) Φ :=
    fun h hh Φ hΦ => hV' 1 h one_mem_uAt hh Φ hΦ

  have bV : ∀ g ∈ UAt σ Γ.V (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), ob (g, 1) Φ = oa (g, 1) Φ :=
    fun g hg Φ hΦ => (lV g hg Φ hΦ).symm
  have bV' : ∀ g ∈ UAt σ Γ.V' (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), ob' (g, 1) Φ = oa' (g, 1) Φ :=
    fun g hg Φ hΦ => (lV' g hg Φ hΦ).symm
  have bW : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), ob (1, h) Φ = oa (1, h) Φ :=
    fun h hh Φ hΦ => (lW h hh Φ hΦ).symm
  have bW' : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), ob' (1, h) Φ = oa' (1, h) Φ :=
    fun h hh Φ hΦ => (lW' h hh Φ hΦ).symm
  refine ⟨⟨hR.quot.onto, ?_, ?_⟩, ⟨hR.quot'.onto, ?_, ?_⟩, ?_, ?_, hR.nontriv, ?_⟩
  · intro γ hγ f hf f₁ h
    exact hR.quot.lie γ hγ f hf f₁ (actsD_of_eqOn (fun t => bV _ (hγ.2 _)) h)
  · intro k hk f hf f₁ h
    exact hR.quot.cpt k hk f hf f₁ (acts_of_eqOn (bV k hk.1) h)
  · intro γ hγ f hf f₁ h
    exact hR.quot'.lie γ hγ f hf f₁ (actsD_of_eqOn (fun t => bV' _ (hγ.2 _)) h)
  · intro k hk f hf f₁ h
    exact hR.quot'.cpt k hk f hf f₁ (acts_of_eqOn (bV' k hk.1) h)
  · intro γ hγ f hf f' hf' f₁ f₁' h h'
    exact hR.lie γ hγ f hf f' hf' f₁ f₁' (actsD_of_eqOn (fun t => bW _ (hγ.2 _)) h)
      (actsD_of_eqOn (fun t => bW' _ (hγ.2 _)) h')
  · intro k hk f hf f' hf' f₁ f₁' h h'
    exact hR.cpt k hk f hf f' hf' f₁ f₁' (acts_of_eqOn (bW k hk.1) h) (acts_of_eqOn (bW' k hk.1) h')
  · intro N h1 h2
    refine hR.irred N (fun γ hγ f hf f₁ h => h1 γ hγ f hf f₁ (actsD_of_eqOn (fun t => lW _ (hγ.2 _)) h))
      (fun k hk f hf f₁ h => h2 k hk f hf f₁ (acts_of_eqOn (lW k hk.1) h))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianMulNatSurjective
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SemiAbSurj

theorem surjective_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {X Y : Over (Sp k)}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [Flat f.left]
    [LocallyOfFinitePresentation f.left]
    (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ Y, ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = y) : Surjective f.left := by
  refine ⟨Set.range_eq_univ.1 ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ := RationalPoint.exists_pt_mem (f.left.isOpenMap.isOpen_range).isClosed_compl
    (Set.nonempty_compl.2 hne)
  obtain ⟨x, rfl⟩ := h y
  exact hy ⟨RationalPoint.pt x, rfl⟩

end GlobalTheory.SemiAbSurj

namespace GlobalTheory.SemiAbSurj

theorem exists_root_unit {k : Type} [Field k] [IsAlgClosed k] (m : ℕ) (hm : m ≠ 0)
    (u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ) : ∃ v : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ, v ^ m = u := by
  let e : Γ((𝟙_ (Over (Sp k))).left, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e u.val) (Nat.pos_of_ne_zero hm)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hz
    exact (u.isUnit.map e).ne_zero hz.symm
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom (Units.mk0 z hz0), Units.ext ?_⟩
  rw [← map_pow, Units.coe_map, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
  exact e.symm_apply_apply u.val

theorem exists_pow_eq_of_torusExtension {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] (E : TorusExtension G) (m : ℕ) (hm : m ≠ 0)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) : ∃ y : 𝟙_ (Over (Sp k)) ⟶ G, y ^ m = x := by
  classical
  letI := E.addCommGroup
  letI := E.free
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  have hB := E.isAbelian
  haveI := hB.smooth
  haveI := hB.comm

  have hsB := GlobalTheory.AbelianLimit.surjective_pow E.B hB m (Nat.one_le_iff_ne_zero.2 hm)
  haveI : LocallyOfFiniteType (((𝟙 E.B) ^ m : E.B ⟶ E.B).left ≫ E.B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType ((𝟙 E.B) ^ m : E.B ⟶ E.B).left := locallyOfFiniteType_of_comp _ E.B.hom
  obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ((𝟙 E.B) ^ m : E.B ⟶ E.B).left (x ≫ E.q).left
  let b' : 𝟙_ (Over (Sp k)) ⟶ E.B := Over.homMk p (by
    have := Over.w (x ≫ E.q)
    rw [hp, Category.assoc, Over.w] at this
    exact this)
  have hb' : b' ^ m = x ≫ E.q := by
    rw [← Category.comp_id b', ← MonObj.comp_pow]
    exact Over.OverMorphism.ext hp.symm

  haveI : LocallyOfFiniteType (E.q.left ≫ E.B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType E.q.left := locallyOfFiniteType_of_comp _ E.B.hom
  haveI := E.q_surjective
  obtain ⟨p', hp'⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective E.q.left b'.left
  let g' : 𝟙_ (Over (Sp k)) ⟶ G := Over.homMk p' (by
    have := Over.w b'
    rw [hp', Category.assoc, Over.w] at this
    exact this)
  have hg' : g' ≫ E.q = b' := Over.OverMorphism.ext hp'.symm

  let qh := IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))
  let ih := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hq : ∀ z, qh z = z ≫ E.q := fun _ => rfl
  have hi : ∀ z, ih z = z ≫ E.i := fun _ => rfl
  let h := x * (g' ^ m)⁻¹
  have hh : h ≫ E.q = 1 := by
    rw [← hq, map_mul, map_inv, map_pow, hq, hq, hg', hb', mul_inv_cancel]
  let s := E.isKernel.lift h (toUnit _) (by rw [hh, Hom.one_def])
  have hs : s ≫ E.i = h := E.isKernel.lift_fst _ _ _
  let e := splitTorusPointsEquiv (Sp k) E.X (𝟙_ (Over (Sp k)))
  obtain ⟨d, hd⟩ := GlobalTheory.TorsionLift.exists_char_root (Module.Free.chooseBasis ℤ E.X) m (e s)
    fun i => exists_root_unit m hm _
  refine ⟨e.symm d ≫ E.i * g', ?_⟩
  rw [mul_pow, ← hi, ← map_pow, ← map_pow, hd, MulEquiv.symm_apply_apply, hi, hs]
  exact inv_mul_cancel_right x (g' ^ m)

end GlobalTheory.SemiAbSurj

namespace GlobalTheory.SemiAbSurj

theorem surjective_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ m : ℕ, m ≠ 0 → Surjective ((𝟙 G) ^ m : G ⟶ G).left := by
  intro S G _ _ hG m hm
  have hfl := (GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow S G hG m hm).1
  haveI := hG.smooth
  refine ⟨fun x => ?_⟩
  let K := AlgebraicClosure (S.residueField (G.hom x))
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField (G.hom x)) K) ≫ S.fromSpecResidueField (G.hom x)
  have ht : G.hom x = t (IsLocalRing.closedPoint K) := (Scheme.fromSpecResidueField_apply _ _).symm
  let B := (Over.pullback t).obj G
  have hP := GlobalTheory.AbelianLimit.isPullback_pow (isGrpPullback_pullback G t) m
  haveI : LocallyOfFiniteType B.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom t))
  haveI : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  haveI : Flat ((𝟙 B) ^ m : B ⟶ B).left := MorphismProperty.of_isPullback hP hfl
  haveI : LocallyOfFiniteType (((𝟙 B) ^ m : B ⟶ B).left ≫ B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType ((𝟙 B) ^ m : B ⟶ B).left := locallyOfFiniteType_of_comp _ B.hom
  haveI : LocallyOfFinitePresentation ((𝟙 B) ^ m : B ⟶ B).left := inferInstance
  obtain ⟨E⟩ := hG.fibres K t
  have hs : Surjective ((𝟙 B) ^ m : B ⟶ B).left := by
    refine surjective_of_rationalPoints _ fun y => ?_
    obtain ⟨z, hz⟩ := exists_pow_eq_of_torusExtension B E m hm y
    exact ⟨z, by rw [MonObj.comp_pow, Category.comp_id, hz]⟩
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback G.hom t) x _ ht
  obtain ⟨z, rfl⟩ := ((𝟙 B) ^ m : B ⟶ B).left.surjective y
  exact ⟨pullback.fst G.hom t z,
    (congrArg (fun g => g z) (GlobalTheory.AbelianLimit.pow_comm (isGrpPullback_pullback G t) m)).symm.trans hy⟩

end GlobalTheory.SemiAbSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortAtFrame
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section
namespace GlobalTheory.FrameShort


open GlobalTheory.PtId GlobalTheory.AdTh in
set_option maxHeartbeats 4000000 in
theorem short_at_frame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ c0' : ℂ, c0' * c0⁻¹ ∈ D.what₂.embLL.range → (∃ m : ℕ, 0 < m ∧ (c0' * c0⁻¹) ^ m = 1) → (∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.ThFr.IsSympl X bas → GlobalTheory.AdTh.IdxIs T.Q.c (O i).s0 X idx e → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk → GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ := ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra; ∀ (y₂ : FrPt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ℂ) (A₂ : GlobalTheory.Dict.AnFib X bas idx e (GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ y₂ = c0' * ((χ xk : Circle) : ℂ)) → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∀ g : GA D (Wc D i), (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) ((F₀).1 : T.R ((i : ℕ) + 1)) g = D.what₂.embLL c * singleSeries R i ω φ' h ((O i).c0' y) w g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 c0' hρ hρm hcT
  have hTi : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hP := hOP.2
  have hs : (O i).s0 = T.J.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.J.Q.c (O i).s0 := hs ▸ T.J.toCore.good_σ₀
  have hmod := models_at_record_core D G Pl0 T0 A T.J R F κ v₀ hC hTi i (O i).s0 hs
  obtain ⟨hemb, hisom, hroot, hmk⟩ := dict_cast T.J hTi.laws _ (inR i) (O i).s0 hσ (Wc D i) (O i).hV (rank_Wc i)
  obtain ⟨δ', hδ'⟩ := GlobalTheory.AdTh.ShortSeriesTw.thetaKO_eq_short_series_tw D G Pl0 T0 A _ R F hC i hP.lift.std _ _ (iotaW T.J i) hemb hisom
  obtain ⟨y₀, ζ, φc, hrk, hζL, hζm, hhat, hphi, hhalf, hbadP⟩ := GlobalTheory.CoverDatum.datum_eq_hat_free D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hβ v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK x₀ hAdm
  obtain ⟨hGf, e, Ps, he, hPs0, hsupp⟩ := hSB
  have hPs : ∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP hm =>
    hPs0 PP hPP (by rw [Nat.cast_mul]; exact PP.asIdeal.mul_mem_right _ hm)
  have hPsO : ∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP hm =>
    hPs0 PP hPP (by rw [Nat.cast_mul]; exact PP.asIdeal.mul_mem_left _ hm)
  obtain ⟨yd, hyd⟩ := exists_isDetAt he (Vc D i) h
  obtain ⟨c1, hc1, hint1⟩ := GlobalTheory.T.twisted_kernel_class_scalar_integral_standard D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h N hUm hTb hTd hLev hLa e Ps yd hGf he hPs hPsO hsupp hyd
  obtain ⟨ρ, hρ'⟩ := hρ
  obtain ⟨ζL, hζL'⟩ := hζL
  have hρm' : ∃ m : ℕ, 0 < m ∧ ρ ^ m = 1 := by
    obtain ⟨m, hm, hm1⟩ := hρm
    refine ⟨m, hm, D.what₂.embLL.injective ?_⟩
    rw [map_pow, hρ', hm1, map_one]
  have hζm' : ∃ m : ℕ, 0 < m ∧ ζL ^ m = 1 := by
    obtain ⟨m, hm, hm1⟩ := hζm
    refine ⟨m, hm, D.what₂.embLL.injective ?_⟩
    rw [map_pow, hζL', hm1, map_one]
  have hroot_int : ∀ z : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → IsIntegral ℤ z ∧ IsIntegral ℤ z⁻¹ := by
    rintro z ⟨m, hm, hz⟩
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hm (hz ▸ isIntegral_one)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hz
      exact zero_ne_one hz
    refine ⟨hzI, ?_⟩
    have e : z⁻¹ = z ^ (m - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hz0, ← pow_succ, Nat.sub_add_cancel hm]
      exact hz
    rw [e]
    exact hzI.pow _
  set d := degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) with hd
  refine ⟨y₀, ((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * c1, hrk, fun lam hlam => ?_, ?_⟩
  · obtain ⟨s, hs, hsi⟩ := hint1 lam hlam
    refine ⟨s, hs, ?_⟩
    have e : (s : D.what₂.LL) * (((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * c1) =
        ((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * ((s : D.what₂.LL) * c1) := by ring
    rw [e]
    exact (((isIntegral_algebraMap (R := ℤ) (x := (((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ))).mul (hroot_int ρ hρm').1).mul
      (hroot_int ζL hζm').2).mul hsi
  intro φ' hφ' w hw F₀ hF₀ g
  have hU' : IsUnf (T.J.U ((i : ℕ) + 1) (O i).s0) := hTi.laws.unf _ (inR i) (O i).s0 hσ
  obtain ⟨hX, hon, hinv, hp, hrk', hpq, h1, hrt, -, hbas, hD, -⟩ := hmod ((O i).dict g).1
  obtain ⟨hx, g', Dc, γ, mk, vv, ϑ, κ', B, hat, hsd, hm, hBm, hma, hϑ, hvv, hκ, hrd⟩ :=
    exists_point (T.J.U ((i : ℕ) + 1) (O i).s0) hσ hU' h1 hTi.laws.pins.2.1.2 R.θ (Vc D i) (Wc D i) (rank_Wc i) (O i).dict
      (iotaW T.J i) (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (fun Wt k => hmk R.θ hC.models.inf (fun k => (hmod k).1) h1 Wt k)
      (wtA (κ i)) hD (O i).mu (R.ωP i A.μ0) (R.vacP i) cc hcc g
  obtain ⟨hγ, hΛ, hfr⟩ := hat
  obtain ⟨xk, hxk⟩ := hroot (γ * g)
  have hζ0 : ζ ≠ 0 := by
    obtain ⟨m, hm, hm1⟩ := hζm
    rintro rfl
    rw [zero_pow hm.ne'] at hm1
    exact zero_ne_one hm1
  letI : Algebra T.Q.c.F ℂ := (O i).s0.toAlgebra
  obtain ⟨mk₂, Y, hm₂, ha₂, hY, hgeo⟩ := GlobalTheory.ShortPtVal.short_value_at_point D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP χ c0' hcT Λ N x₀ P hUm hTb hTd hLev hAdm
    hPh' ζ φc hζ0 hhat F₀.1 hF₀ _ g' Dc (γ * g) xk hxk hX hp hΛ hsd _ hx hfr mk hm hma vv ϑ κ' hvv hκ _ B hBm hϑ
  obtain ⟨vr, hvr⟩ := exists_isVarOf (Vc D i) (Wc D i) (rank_Wc i) _ hX _ Dc.hr
  have hCs := GlobalTheory.AdTh.VecSeries.singleSeries_eq_phase_thetaKO D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hIo χ ω hK.weil _ _ φ' hφ' ka hka P y hio _ g' Dc vr hX hp hvr h w hw g γ hγ
  have htw := GlobalTheory.OnCmp.weil_twist_base_of D G Pl0 T0 A _ R F hC i χ ω hK.weil (γ * g) xk hxk (R.vacP i) (hC.thP.vP i A.μ0).1.2.theta
  have hrd' : Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) ((T.J.U ((i : ℕ) + 1) (O i).s0).X ((O i).dict g).1) Dc.bas Dc.idx
      (ω (1, γ * g) (R.vacP i)) ((((χ xk : Circle) : ℂ) * (cc ((O i).dict g).1 * (O i).mu g * κ')) • vv) ((O i).dict g).2 := by
    obtain ⟨s1, s2⟩ := ((thA_heis_entire_linear_injective _ _ g' _ _ Dc.bas Dc.idx Dc.sympl hD.2 _ hx _ hrd.1).2.2 vv hvv.1).1
      ((χ xk : Circle) : ℂ) 0
    rw [zero_smul, add_zero, smul_smul] at s1 s2
    rw [zero_smul, add_zero] at s2
    refine ⟨s1, fun z hz => ?_⟩
    rw [htw, s2, Pi.smul_apply, Pi.smul_apply, hrd.2 z hz, smul_eq_mul, smul_eq_mul]
    ring
  have hH := hPh'.1
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)).IsHomogeneous d :=
    ((isHomogeneous_of_rowDeg _ _ _ _ hH.2.2).map _).rename_isHomogeneous
  have hser := hδ' χ _ _ ω φ' hK.weil _ hK.chr hK.fin hK.ram hK.pl (GlobalTheory.OnCmp.readsOnly_omegaFree R i _ ξR y₀) hφ' _ φc hphi
    hhalf hrt g' _ _ Dc.hr Dc.bas Dc.idx _ vr hX Dc.sympl hon hinv (hbas _) hvr
    (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) N h (γ * g) Λ mk₂ e Ps yd hbadP he hPs hGf hsupp hyd hLa hTd hLev ha₂
    Y (hΛ ▸ hY) vv _ (hΛ ▸ hvv) (hfr ▸ hrd') _ d hhom
  rw [hΛ, ← hfr] at hser
  have hx0 : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hrdU : rdU (T.J.U ((i : ℕ) + 1) (O i).s0) (F₀.1 : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 = _ :=
    (dif_pos hx).trans hgeo
  have hphiE : (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ d * c0⁻¹) • cc) (F₀.1 : T.R ((i : ℕ) + 1)) g =
      ((ka * (-((δ : ℤ) : ℂ)) ^ d * c0⁻¹) * cc ((O i).dict g).1) * (O i).mu g *
        rdU (T.J.U ((i : ℕ) + 1) (O i).s0) (F₀.1 : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 := rfl
  have hSS := hCs.trans (congrArg (fun z => ka * z) hser)
  rw [hphiE, hrdU, hSS, GlobalTheory.AdTh.SerCore.lieFac_eq_sqrt_pow _ hx0, ← hc1]
  simp only [map_mul, map_inv₀, map_intCast, hρ', hζL']
  have hδ2 : ((δ' : ℤ) : ℂ) ^ d * ((δ' : ℤ) : ℂ) ^ d = 1 := by
    rw [← mul_pow]
    rcases Int.units_eq_one_or δ' with e | e <;> rw [e] <;> simp
  push_cast
  have alg : ∀ (s ka δc δc' c0 c0' k m x c1 a b q κ' ζ TH : ℂ) (n : ℕ), δc' ^ n * δc' ^ n = 1 →
      s ^ n * (ka * (-δc) ^ n * c0⁻¹ * k * m * (c0' * x * (c1 * (a * b * q) * κ' * ζ⁻¹ * TH))) =
        (δc * δc') ^ n * (c0' * c0⁻¹) * ζ⁻¹ * c1 * (ka * (δc' ^ n * (-1) ^ n * s ^ n * (x * (k * m * κ')) * (a * b) * q * TH)) := by
    intro s ka δc δc' c0 c0' k m x c1 a b q κ' ζ TH n hn
    rw [neg_pow, mul_pow]
    linear_combination (-(s ^ n * ka * (-1) ^ n * δc ^ n * c0⁻¹ * k * m * c0' * x * c1 * a * b * q * κ' * ζ⁻¹ * TH)) * hn
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hδ2

end GlobalTheory.FrameShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMapIntegrableDistribution
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.HaarPull

open GlobalTheory.DiagForm GlobalTheory.DiagUniq

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

variable {F : Type} [Field F] [NumberField F] {ι κ : Type} [Fintype ι] [Fintype κ]

theorem pureA_mulVec_glue (D : Matrix κ ι F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (p : Vi F ι × Vf F ι) :
    pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p) =
      f (fun k => ∑ i, mixedEmbedding F (D k i) * eI F ι p.1 i) *
      g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ p.2) := by
  unfold pureA
  congr 2 <;> funext k
  · refine ((map_sum ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
        (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
        (fun i => algebraMap F (AF F) (D k i) * glue p i) Finset.univ)).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (map_mul _ _ _).trans ?_
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (D k i)) *
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F ι p.1 i)) = _
    rw [RingEquiv.apply_symm_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  · exact (map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => algebraMap F (AF F) (D k i) * glue p i) Finset.univ)

theorem integrable_SB {g : Vf F ι → ℂ} (hg : g ∈ SB (Vf F ι)) : Integrable g Measure.addHaar :=
  hg.1.continuous.integrable_of_hasCompactSupport hg.2

theorem pureA_glue_eq (D : Matrix κ ι F)
    (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ)
    (hT : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : ι → mixedEmbedding.mixedSpace F),
        T f a = f (fun k => ∑ i, mixedEmbedding F (D k i) * a i))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    (fun p : Vi F ι × Vf F ι => pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p)) =
      fun p => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f) p.1 *
        g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ p.2) := by
  funext p
  rw [pureA_mulVec_glue, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hT]

theorem integrable_glue (D : Matrix κ ι F) (hD : ∀ z : ι → F, D *ᵥ z = 0 → z = 0)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Integrable (fun p : Vi F ι × Vf F ι => Φ (D.map (algebraMap F (AF F)) *ᵥ glue p)) (mu F ι) := by
  obtain ⟨T, hT⟩ := GlobalTheory.ArchPull.exists_pull F ι κ D hD
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    rw [pureA_glue_eq D T hT f g]
    exact (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f)).integrable.mul_prod
      (integrable_SB (GlobalTheory.FinPull.pullback_mem_SB F ι κ D hD g hg))
  | zero => exact integrable_zero _ _ _
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

end GlobalTheory.HaarPull

namespace GlobalTheory

open GlobalTheory.DiagForm GlobalTheory.DiagUniq GlobalTheory.HaarPull

theorem integral_pull_injective : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∀ ν : @Measure (ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      (∀ Φ ∈ schA F κ, (letI : MeasurableSpace (ι → AF F) := borel _;
        Integrable (fun w => Φ (D.map (algebraMap F (AF F)) *ᵥ w)) ν)) ∧
      ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, (letI : MeasurableSpace (ι → AF F) := borel _;
          ∫ w, pureA F f g (D.map (algebraMap F (AF F)) *ᵥ w) ∂ν) = T f := by
  intro F _ _ ι κ _ _ D hD ν hν
  letI : MeasurableSpace (ι → AF F) := borel _
  haveI : BorelSpace (ι → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hν
  haveI : ((mu F ι).map (glueE F ι)).IsAddHaarMeasure := (glueE F ι).isAddHaarMeasure_map _
  have h := Measure.isAddLeftInvariant_eq_smul ν ((mu F ι).map (glueE F ι))
  set c := Measure.addHaarScalarFactor ν ((mu F ι).map (glueE F ι))
  have me := (glueE F ι).toHomeomorph.measurableEmbedding
  refine ⟨fun Φ hΦ => ?_, fun g hg => ?_⟩
  · rw [h]
    refine Integrable.smul_measure_nnreal ?_
    exact me.integrable_map_iff.2 (integrable_glue D hD hΦ)
  · obtain ⟨T, hT⟩ := GlobalTheory.ArchPull.exists_pull F ι κ D hD
    refine ⟨(((c : ℝ) : ℂ) * ∫ v, g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ v) ∂(Measure.addHaar : Measure (Vf F ι))) •
      ((SchwartzMap.integralCLM ℂ (volume : Measure (Vi F ι))).comp
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι)).comp T)), fun f => ?_⟩
    rw [h, integral_smul_nnreal_measure]
    change c • ∫ x, pureA F f g (D.map (algebraMap F (AF F)) *ᵥ x) ∂((mu F ι).map (glueE F ι).toHomeomorph) = _
    rw [me.integral_map]
    have e := pureA_glue_eq D T hT f g
    change c • ∫ p, (fun p : Vi F ι × Vf F ι => pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p)) p ∂(mu F ι) = _
    rw [e, mu, integral_prod_mul (fun u : Vi F ι => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f) u)
      (fun v : Vf F ι => g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ v))]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
      smul_eq_mul, NNReal.smul_def, Complex.real_smul]
    ring

end GlobalTheory
end
end

