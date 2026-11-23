module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0103
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFinPartILocFEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a → a = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by
  intro h
  refine Prod.ext ?_ ?_
  · have h1 := h ((1 : Ainf F), (0 : Af F)) (by
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (0 : Af F) = 0
      exact map_zero _)
    have h2 := congrArg Prod.fst h1
    change (1 : Ainf F) * a.1 = 0 at h2
    rw [one_mul] at h2
    rw [h2]
    rfl
  · refine GlobalTheory.AdelicU.af_ext fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w a.2 =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.AdelicU.singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a.2))
    by_cases e : w = v
    · subst e
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e]
      have h1 := h ((0 : Ainf F), GlobalTheory.AdelicU.singleFin w 1) (by
        change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (GlobalTheory.AdelicU.singleFin w 1) = 0
        exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm e) 1)
      have h2 := congrArg (fun x : AF F => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w x.2) h1
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.AdelicU.singleFin w 1 * a.2) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w 0 at h2
      rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul, map_zero] at h2
      exact h2

end GlobalTheory.VacAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddCharThetaCommutatorPhaseSkewLattice
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CommPhase

theorem kap_add (D : D7) (T : Tor D) {N N' : ℕ} (x y z : VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.kap D T x (y + z) = Formalism.MainNotions.TaylorLogMetric.kap D T x y * Formalism.MainNotions.TaylorLogMetric.kap D T x z := by
  simp only [Formalism.MainNotions.TaylorLogMetric.kap, GlobalTheory.NormSum.VacMove.hf_add_right, Complex.add_im, Complex.ofReal_add, mul_add,
    Complex.exp_add]

theorem kap_eq_one_of_int (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (m : ℤ)
    (h : (Hf D T x y).im = m) : Formalism.MainNotions.TaylorLogMetric.kap D T x y = 1 := by
  rw [Formalism.MainNotions.TaylorLogMetric.kap, h]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (((m : ℝ)) : ℂ) = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem chars : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}, ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), ∃ χ : AddChar ((La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) ℂ, ∀ y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), χ (y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d) := by
  intro D δ hc 𝔪 a d x hx
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D a) (GlobalTheory.NormSum.VacMove.moves_one D d)
  have hint : ∀ y ∈ La0 D (tor0 D ⊤ δ) a d, ∃ m : ℤ, (Hf D (tor0 D ⊤ δ) x y).im = m :=
    (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hc a d _ k0).2.2.1 x hx
  set Lp := La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)
  set S := (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf Lp
  have hwd : ∀ u v : Lp, (QuotientAddGroup.leftRel S) u v →
      Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (u : VC D a d) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (v : VC D a d) := by
    intro u v huv
    rw [QuotientAddGroup.leftRel_apply] at huv
    have hm : ((-u + v : Lp) : VC D a d) ∈ La0 D (tor0 D ⊤ δ) a d := AddSubgroup.mem_addSubgroupOf.mp huv
    obtain ⟨m, hm⟩ := hint _ hm
    have h1 := kap_eq_one_of_int D (tor0 D ⊤ δ) x _ m hm
    have hv : (v : VC D a d) = (u : VC D a d) + ((-u + v : Lp) : VC D a d) := by
      push_cast; abel
    rw [hv, kap_add, h1, mul_one]
  let χ : AddChar (Lp ⧸ S) ℂ :=
    { toFun := fun q => Quotient.liftOn' q (fun y : Lp => Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d)) hwd
      map_zero_eq_one' := by
        show Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((0 : Lp) : VC D a d) = 1
        exact kap_eq_one_of_int D (tor0 D ⊤ δ) x _ 0 (by simp [Hf])
      map_add_eq_mul' := by
        intro q r
        induction q using QuotientAddGroup.induction_on
        induction r using QuotientAddGroup.induction_on
        rename_i u v
        show Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((u + v : Lp) : VC D a d) =
          Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (u : VC D a d) * Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (v : VC D a d)
        push_cast
        exact kap_add _ _ _ _ _ }
  exact ⟨χ, fun y => rfl⟩

end GlobalTheory.CommPhase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharPSpecialisationSmoothCommGroupCurve
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CharPSpec

theorem spMap_comp_eq' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem exists_charP_specialization : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (p : ℕ) (_ : Fact p.Prime) (_ : CharP k' p) (G' : Over (Sp k')) (_ : GrpObj G'), GlobalTheory.SS.SmConn G' ∧ SmoothOfRelativeDimension g G'.hom ∧ (m : k') ≠ 0 ∧ (∃ s' : Finset (𝟙_ (Over (Sp k')) ⟶ G'), (∀ x ∈ s', x ^ m = 1) ∧ s'.card = s.card) ∧ ∃ (P' : Polynomial k') (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ G'.left) (a' b' : Localization.Away P' →ₐ[k'] k'), u' ≫ G'.hom = spMap (algebraMap k' (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  intro k _ _ _ G _ hG g hg m hm s hs P hP u a b hu hab
  classical
  have hm0 : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨R, G₁, _, hfg, hmR, hcomm, hsm, hsep, hqc, hgc, hrd, ⟨s₁, hcard, hs₁, hdist⟩, P₁, hP₁, u₁, α, β, hα, hβ,
    hu₁, hαβ⟩ := GlobalTheory.T.exists_fg_subring_descent_group_sections_curve k G hG g hg m hm hm0 s hs P hP u a b hu hab
  haveI : Algebra.FiniteType ℤ R := hfg
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hinj : Function.Injective R.subtype := Subtype.val_injective
  obtain ⟨f₁, hf₁, H₁⟩ := _root_.GlobalTheory.SmoothRelDim.exists_basicOpen R G₁ hsm hqc k R.subtype hinj g hrd
  obtain ⟨f₂, hf₂, H₂⟩ := _root_.GlobalTheory.SpreadConn.geometricallyConnected_of_generic R G₁ hsm hqc k R.subtype hinj hgc
  obtain ⟨f₃, hf₃, H₃⟩ := _root_.GlobalTheory.SectionsSpread.pairs R G₁ hsep k R.subtype hinj (s₁.image fun x => x.left)
    (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact Over.w y)
    (by
      intro x hx y hy hxy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      exact hdist x' hx' y' hy' fun h => hxy (by rw [h]))
  have hsec : ∀ (c₀ : R) (hc₀ : IsUnit (Polynomial.evalRingHom c₀ P₁)),
      spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hc₀) ≫ u₁ ≫ G₁.hom = 𝟙 _ := by
    intro c₀ hc₀
    rw [hu₁, spMap_comp_eq' (h := RingHom.id R)]
    · show Spec.map (CommRingCat.ofHom (RingHom.id R)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    · ext r
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away P₁),
        IsLocalization.Away.lift_eq]
      simp
  obtain ⟨f₄, hf₄, H₄⟩ := _root_.GlobalTheory.SectionsSpread.pairs R G₁ hsep k R.subtype hinj
    {spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁,
      spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁}
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [Category.assoc]; exact hsec α hα
      · rw [Finset.mem_singleton.mp hx, Category.assoc]; exact hsec β hβ)
    (by
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd rfl hxy
      · rw [Finset.mem_singleton.mp hy]; exact hαβ
      · rw [Finset.mem_singleton.mp hx]; exact Ne.symm hαβ
      · rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy] at hxy; exact absurd rfl hxy)
  have hlc : R.subtype P₁.leadingCoeff ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP₁
  set f := f₁ * f₂ * f₃ * f₄ * P₁.leadingCoeff with hfdef
  have hf : f ≠ 0 := by
    intro h
    have := congrArg R.subtype h
    rw [map_zero, hfdef] at this
    simp only [map_mul] at this
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hf₁ hf₂) hf₃) hf₄) hlc) this
  obtain ⟨M, hM, hfM, p, hp, hpM⟩ := _root_.GlobalTheory.closedPt_of_finiteType_int R f hf
  letI := Ideal.Quotient.field M
  let ψ : R →+* AlgebraicClosure (R ⧸ M) := (algebraMap (R ⧸ M) _).comp (Ideal.Quotient.mk M)
  have hψ : ∀ r, r ∉ M → IsUnit (ψ r) := by
    intro r hr
    refine isUnit_iff_ne_zero.mpr ?_
    rw [RingHom.comp_apply, map_ne_zero_iff _ (algebraMap (R ⧸ M) _).injective]
    exact fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hu := hψ f hfM
  simp only [hfdef, map_mul, IsUnit.mul_iff] at hu
  obtain ⟨⟨⟨⟨u1, u2⟩, u3⟩, u4⟩, u5⟩ := hu
  haveI : Fact p.Prime := ⟨hp⟩
  have hpF : CharP (AlgebraicClosure (R ⧸ M)) p := by
    rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast ψ, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpM, map_zero]
  refine ⟨AlgebraicClosure (R ⧸ M), inferInstance, inferInstance, p, inferInstance, hpF,
    (Over.pullback (spMap ψ)).obj G₁, inferInstance, ?_, H₁ _ ψ u1, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, ?_, ?_, ?_, H₂ _ ψ u2⟩
    · show Smooth (pullback.snd _ _); infer_instance
    · show IsSeparated (pullback.snd _ _); infer_instance
    · show QuasiCompact (pullback.snd _ _); infer_instance
  · rw [← map_natCast ψ]
    exact (hmR.map ψ).ne_zero
  · refine ⟨s₁.image (GlobalTheory.IsogRed.sec (spMap ψ)), ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rw [← GlobalTheory.IsogRed.sec_pow, hs₁ y hy]
      simpa using (GlobalTheory.IsogRed.sec_pow (spMap ψ) y 0).trans (pow_zero _)
    · rw [← hcard]
      refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
      by_contra hne
      have e := congrArg (fun z => z.left ≫ pullback.fst G₁.hom (spMap ψ)) hxy
      simp only [GlobalTheory.IsogRed.sec_left] at e
      exact H₃ _ ψ u3 x.left (Finset.mem_image_of_mem _ hx) y.left (Finset.mem_image_of_mem _ hy)
        (fun h => hne (Over.OverMorphism.ext h)) e
  · exact GlobalTheory.T.curve_baseChange_two_distinct_points_of_field R _ ψ G₁ P₁ u₁ α β hα hβ hu₁ u5
      (H₄ _ ψ u4 _ (Finset.mem_insert_self _ _) _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (fun h => hαβ (by rw [h])))

end GlobalTheory.CharPSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFrameDeformationOfDerivationCombinati
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem GlobalTheory.HorFrame.exists_deform_of_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁) (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ {ι : Type} [Fintype ι] (d : ι → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → ∀ (Mx : ι → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →+* K) (hk : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K), X.F.ChartFr k _ hk Q → ∀ (θ : Γ(M.X, W₁) →+* DualNumber K) (m : ι → K), (∀ s, (θ s).fst = ψ s) → (∀ s, (θ s).snd = ∑ a, m a * ψ (d a s).snd) → ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (∑ a, m a • (ψ ∘ Mx a)) ∧ spMap θ ≫ tau hW₁ ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hk₁ _ Q₀ hQ₀ ι _ d hd Mx hMx K _ _ ψ hk Q hQ θ m hθ1 hθ2
  haveI := c.fin
  have hinj : ∀ {A B : Type} [CommRing A] [CommRing B] (f g : A →+* B), spMap f = spMap g → f = g := by
    intro A B _ _ f g h
    have := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom this
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hjs : ∀ {T : Type} [CommRing T] [Algebra c.F T] (P : FrPt Xo c T),
      frX P ≫ Y.j ≫ Y.s = spMap (algebraMap c.F T) := by
    intro T _ _ P
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, frX_snd,
      hid, Category.comp_id]
  have e1 : frX Q ≫ Y.j = spMap ψ ≫ frX Q₀ ≫ Y.j := by
    rw [hQ.over, hQ₀.over]; simp only [Category.assoc]
  have hψα : ψ.comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F K := by
    have h2 := congrArg (· ≫ Y.s) e1
    simp only [Category.assoc] at h2
    rw [hjs Q, hjs Q₀, spMap_comp'] at h2
    exact (hinj _ _ h2).symm

  let ψA : Γ(M.X, W₁) →ₐ[c.F] K := ⟨ψ, fun r => RingHom.congr_fun hψα r⟩
  have hfrX : frX Q = spMap ψ ≫ frX Q₀ := by
    refine xF_ext (Y := Y) (frX_snd Q) ?_ (by rw [e1, Category.assoc])
    rw [Category.assoc, frX_snd, spMap_comp', hψα]
  have hQx : Q.x = spMap ψ ≫ Q₀.x := by
    rw [← frX_fst, hfrX, Category.assoc, frX_fst]
  have hFQ : FrMap ψA Q₀ Q := by
    obtain ⟨Q', hQ'⟩ := exists_frMap ψA Q₀
    have hc := hQ₀.frMap hQ' (z' := (spMap ψ ≫ tau hW₁) ≫ toFlag M) (by simp only [Category.assoc]) hk
    rwa [hc.unique hQ] at hQ'

  have hdu : ∀ φ : Γ(M.X, W₁) →+* DualNumber K, (∀ s, (φ s).fst = ψ s) →
      φ.comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F (DualNumber K) := by
    intro φ hφ
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · rw [RingHom.comp_apply, hφ, ← RingHom.comp_apply, hψα]; simp [TrivSqZeroExt.algebraMap_eq_inl']
    · rw [_root_.GlobalTheory.ringHom_dualNumber_snd_eq_zero c.F (φ.comp (algebraMap c.F _)) a]; simp [TrivSqZeroExt.algebraMap_eq_inl']
  let θA : Γ(M.X, W₁) →ₐ[c.F] DualNumber K := ⟨θ, fun r => RingHom.congr_fun (hdu θ hθ1) r⟩
  obtain ⟨w, hw⟩ := exists_frMap θA Q₀
  have hwc : X.F.ChartFr k (spMap θ ≫ tau hW₁ ≫ toFlag M) (le_preimage_comp _ hk₁) w :=
    hQ₀.frMap hw rfl _
  have hwpt : spMap θ ≫ tau hW₁ ≫ toFlag M = X.ptY w := FlagCover.eq_ptY hwc.lies
  have hwx : w.x = spMap θ ≫ Q₀.x := by
    rw [← frX_fst, ← frX_frMap hw, Category.assoc, frX_fst]
  have hred : (GlobalTheory.FlagTan.red c K).toRingHom.comp θ = ψ := RingHom.ext fun s => hθ1 s
  have hdef : IsDef Q w := by
    obtain ⟨Q', hQ'⟩ := exists_frMap (GlobalTheory.FlagTan.red c K) w
    have hc := hwc.frMap hQ' (z' := (spMap ψ ≫ tau hW₁) ≫ toFlag M)
      (by rw [← Category.assoc, spMap_comp', hred]; simp only [Category.assoc]) hk
    show FrMap _ w Q
    rwa [hc.unique hQ] at hQ'

  have hθc1 : ∀ a s, (((dualMap ψ).comp (d a)) s).fst = ψ s := by
    intro a s; simp [dualMap, hd]
  have hTan : ∀ φ : Γ(M.X, W₁) →+* DualNumber K, (∀ s, (φ s).fst = ψ s) →
      GlobalTheory.FlagTan.IsTanX Q (spMap φ ≫ Q₀.x) := by
    intro φ hφ
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, Q₀.x_over]
      unfold sOf
      rw [spMap_comp', ← RingHom.comp_assoc, hdu φ hφ]
    · rw [← Category.assoc, spMap_comp', hQx]
      have : (GlobalTheory.FlagTan.red c K).toRingHom.comp φ = ψ := RingHom.ext fun s => hφ s
      rw [this]
  have hKSa : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) Q (spMap ((dualMap ψ).comp (d a)) ≫ Q₀.x) (ψ ∘ Mx a) := by
    intro a
    have := hMx a K ψA Q hFQ
    rwa [← Category.assoc, spMap_comp'] at this
  refine ⟨w, hdef, ?_, hwpt⟩
  rw [hwx]
  refine _root_.GlobalTheory.FlagTan.IsKS.sum_of_der (hKS K Q) (x := fun a => spMap ((dualMap ψ).comp (d a)) ≫ Q₀.x)
    (fun a => hTan _ (hθc1 a)) hKSa (hTan θ hθ1) m ?_
  intro O f h' hc
  exact GlobalTheory.T.evalRingPoint_dualNumber_snd_linear_derivation Q₀.x ψ (fun a => (dualMap ψ).comp (d a)) θ m hθc1 hθ1
    (fun s => by rw [hθ2 s]; simp [dualMap]) O f h' hc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreLinearHomsPrincipalCMTriple
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.GramBaseChange

theorem exists_complex_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ (A' B' : PAT H (Sp ℂ)) (f₁' f₂' : A'.t.G ⟶ B'.t.G) (p' q' : ℕ), p' + q' = p + q ∧ (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ p') ∧ (τ H.rt ≠ H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ q')) ∧ Serre.IsLinearHom A'.t.act B'.t.act f₁' ∧ Serre.IsLinearHom A'.t.act B'.t.act f₂' ∧ ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) → WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ ρ σ₁ A B p q hρ hA f₁ f₂ hf₁ hf₂
  have hβi : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨⟨A', mA, -⟩, hA2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) A
  obtain ⟨⟨B', mB, -⟩, hB2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) B
  obtain ⟨-, -, wA, hwA⟩ := hA2 A' mA inferInstance
  obtain ⟨-, -, wB, hwB⟩ := hB2 B' mB inferInstance
  haveI := hf₁.isMonHom
  haveI := hf₂.isMonHom
  obtain ⟨f₁', hm₁, e₁⟩ := GlobalTheory.PairingFibre.exists_hom mA.cart mB.cart f₁
  obtain ⟨f₂', hm₂, e₂⟩ := GlobalTheory.PairingFibre.exists_hom mA.cart mB.cart f₂
  have lin : ∀ (f : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G), Serre.IsLinearHom A.t.act B.t.act f → IsMonHom f' →
      f'.left ≫ mB.φ = mA.φ ≫ f.left → Serre.IsLinearHom A'.t.act B'.t.act f' := by
    intro f f' hf hm e
    refine ⟨hm, fun c => ?_⟩
    apply Over.OverMorphism.ext
    apply mB.cart.1.hom_ext
    · have hc := congrArg CommaMorphism.left (hf.comm c)
      simp only [Over.comp_left] at hc ⊢
      rw [Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c,
        ← Category.assoc, ← Category.assoc, e]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  have hlie : ∀ (τ : 𝓞 E →+* ℂ) (n : ℕ), LieMult A'.t.act (𝟙 (Sp ℂ)) τ n ↔
      LieMult A.t.act (spMap (σ₁.comp (algebraMap (𝓞 K) K))) τ n := fun τ n => by
    have := GlobalTheory.lieMult_iff_of_isGrpPullback mA.cart A'.t.act A.t.act mA.act (𝟙 (Sp ℂ)) τ n
    rwa [Category.id_comp] at this
  have hweil : ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) →
      WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
    intro g h
    have := (GlobalTheory.PairingFibre.weilEq_iff (g₂ := 𝟙 _) mA.cart mA.cart mB.cart mA.cart B.t.PP.isLB A.t.PP.isLB B'.t.PP.isLB
      A'.t.PP.isLB ⟨wB, hwB.1⟩ ⟨wA, hwA.1⟩ e₁ e₂ (mA.act g) (by simp) (𝟙 (Sp ℂ))).1 h
    rwa [Category.id_comp] at this
  have hT := hA ℂ (σ₁.comp (algebraMap (𝓞 K) K)) hβi
  have hd0 : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h0 => hd0 (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)
  have hsq : ∀ x : ℂ, x ^ 2 = -(H.d : ℂ) → x = H.rt0 ∨ x = -H.rt0 := fun x hx =>
    sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans H.sqrt_neg_disc_sq.symm)
  have hβρ : (σ₁.comp (algebraMap (𝓞 K) K)) ρ ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hρ]; simp
  have hτ : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq]; simp
  have hne : H.rt0 ≠ -H.rt0 := fun h => hr0 (by linear_combination h / 2)
  rcases hsq _ hβρ with hc | hc
  · refine ⟨A', B', f₁', f₂', p, q, rfl, fun τ => ⟨fun ht => ?_, fun ht => ?_⟩,
      lin f₁ f₁' hf₁ hm₁ e₁, lin f₂ f₂' hf₂ hm₂ e₂, hweil⟩
    · exact (hlie τ p).2 ((hT τ).1 (ht.trans hc.symm))
    · exact (hlie τ q).2 ((hT τ).2 (fun h => ht (h.trans hc)))
  · refine ⟨A', B', f₁', f₂', q, p, add_comm _ _, fun τ => ⟨fun ht => ?_, fun ht => ?_⟩,
      lin f₁ f₁' hf₁ hm₁ e₁, lin f₂ f₂' hf₂ hm₂ e₂, hweil⟩
    · exact (hlie τ q).2 ((hT τ).2 (fun h => hne (ht.symm.trans (h.trans hc))))
    · rcases hsq _ (hτ τ) with h | h
      · exact absurd h ht
      · exact (hlie τ p).2 ((hT τ).1 (h.trans hc.symm))

end GlobalTheory.GramBaseChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantWeightShiftFlatLineDet
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatShift

theorem flat_step {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) (ρ : E →+* ℂ) (i j : ℕ) (hi : i < Dw.mult ρ) (hj : j < Dw.mult ρ) :
    (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = (wtOf Dw (flatWt Dw τ) 0).1 (ρ, j) ∧
      -1 ≤ (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) := by
  simp only [wtOf, flatWt, parWt, Datum.mult] at hi hj ⊢
  split_ifs at hi hj ⊢ <;> omega

theorem exists_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H), Dom a n → (∀ ρ i, i < Dw.mult ρ → 2 ≤ a (ρ, i)) → ∃ a' : (E →+* ℂ) × ℕ → ℕ, Dom a' n ∧ (∀ ρ i, i < Dw.mult ρ → 1 ≤ a' (ρ, i)) ∧ exZ Dw (wtZ a' n) = exZ Dw (wtZ a n + wtOf Dw (flatWt Dw τ) 0) := by
  intro E _ _ _ H Dw a n τ hD ha
  refine ⟨fun x => if x.2 < Dw.mult x.1 then ((a x : ℤ) + (wtOf Dw (flatWt Dw τ) 0).1 x).toNat else 0,
    ⟨fun ρ i j hij => ?_, hD.2⟩, fun ρ i hi => ?_, ?_⟩
  · by_cases hj : j < Dw.mult ρ
    · have hi : i < Dw.mult ρ := lt_of_le_of_lt hij hj
      have h1 : a (ρ, j) ≤ a (ρ, i) := hD.1 ρ hij
      obtain ⟨e, -⟩ := flat_step Dw τ ρ i j hi hj
      simp only [if_pos hi, if_pos hj]
      omega
    · simp only [if_neg hj]; exact Nat.zero_le _
  · have h1 := ha ρ i hi
    have h2 := (flat_step Dw τ ρ i i hi hi).2
    simp only [if_pos hi]
    omega
  · funext x
    rcases x with _ | ⟨ρ, i⟩
    · simp [exZ, wtZ, wtOf_snd]
    · have h1 := ha ρ i i.2
      have h2 := (flat_step Dw τ ρ i i i.2 i.2).2
      simp only [exZ, wtZ, Prod.fst_add, Pi.add_apply, if_pos i.2]
      omega

end GlobalTheory.FlatShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUAlphaH
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
noncomputable section

namespace GlobalTheory.FunObj.SqNum

theorem exists_heckeU_alphaH : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ →
    ∀ (G : GridData L sc) (i j : Fin D.R.m), ∃ χ : HeckeU D (botSmall D i j),
      ∀ x, χ.f x = (alphaH L μ₀ i j).1 (finIdl D x) := by
  intro D T L sc μ₀ hL _ i j
  obtain ⟨χ₁, h1, -⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_of_isMu0 (N := 0) ⟨0, rfl⟩ (L.C.isMu0 j) fun g => (D.hc _).e_int j
  have hr := (ranks_exact D i j).2.1
  rcases Nat.mod_two_eq_zero_or_one (rankV D i j) with h | h
  · refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₁ (GlobalTheory.Mem.Col2.SplitChar.trivial D (N := 0) ⟨0, rfl⟩)
      (Int.even_iff.2 (by omega)), fun x => ?_⟩
    rw [GlobalTheory.AlphaSplit.mulU_f, h1]
    simp [alphaH, h, hL.xi_base, GlobalTheory.Mem.Col2.SplitChar.trivial]
  · refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₁ (GlobalTheory.AlphaSplit.etaU L.C.isEta) (Int.even_iff.2 (by omega)), fun x => ?_⟩
    rw [GlobalTheory.AlphaSplit.mulU_f, h1, GlobalTheory.AlphaSplit.etaU_f]
    simp [alphaH, h, hL.xi_base]

end GlobalTheory.FunObj.SqNum
end
end

