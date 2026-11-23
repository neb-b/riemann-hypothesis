module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2609
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMatrixTorsionAdjointOnCharacters
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section
namespace GlobalTheory.Poinc.FibMatrix

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ sc : ℝ, 0 < sc → ∀ j : u.D.toPre.X ≃+ (Fin 8 → X₀), (∀ χ, l.q χ = sc * (qW W β (j χ) : ℤ)) → ∀ (e : ρ.P.A ⟶ ρ.P.A) (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ e.left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) → ∀ (F : u.G ⟶ u.G) (eA : u.A.A ⟶ u.A.A), IsMonHom F → eA.left ≫ u.φ = u.φ ≫ e.left → eA.left ≫ genMap u.U = genMap u.U ≫ F.left → ∀ m : u.D.toPre.X →+ u.D.toPre.X, EndChar u.U F m → ∀ χ, j (m χ) = fun a => ∑ b, E' a b • j χ b := by
  intro o Ω _ _ _ S ρ p _ y₀ u l W hW X₀ _ β hβs hβp sc hsc j hq e E E' hEE hlab F eA hF heA hgen m hm χ
  have hCZ : CharZero u.V :=
    RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hBase : GlobalTheory.Mum.Base u.V := ⟨⟨inferInstance, inferInstance, inferInstance, u.complete⟩, hCZ⟩
  let Em : (Fin 8 → X₀) →+ (Fin 8 → X₀) :=
    { toFun := fun y a => ∑ b, E a b • y b
      map_zero' := by ext; simp
      map_add' := fun y y' => by ext; simp [smul_add, Finset.sum_add_distrib] }
  have hEm : ∀ y, Em y = fun a => ∑ b, E a b • y b := fun _ => rfl
  let s : u.D.toPre.X →+ u.D.toPre.X := (j.symm.toAddMonoidHom.comp Em).comp j.toAddMonoidHom
  have hs : ∀ x, j (s x) = Em (j x) := fun x => by simp [s]
  have hlab' : ∀ (k : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) k) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A),
      1 ≤ k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk' x' →
      x'.left = x.left ≫ eA.left → CongMod k pk'.y (s pk.y) := by
    intro k pk pk' x x' hk hx hx' hxx
    obtain ⟨w, hw⟩ := hlab k pk pk' x x' hk hx hx' (by rw [hxx, Category.assoc, heA])
    refine ⟨j.symm w, j.injective ?_⟩
    rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, hs, hw, hEm]
  have hT := GlobalTheory.T.labelCongruence_endo_all_algClosed_fields o Ω S ρ p y₀ u eA s hlab'
  haveI : Mono (jK u.V) := GlobalTheory.PolDeg.Wit.mono_jK
  haveI : Mono (genMap u.U) := by unfold genMap; infer_instance
  have hTor := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar u.V hBase u.G u.semi u.D u.A u.U F hF m hm
  have hmain := GlobalTheory.TauFormHom.main u.V hBase inferInstance u.G u.semi u.D u.A u.U u.G u.semi u.D u.A u.U F hF m s hTor
    (by
      intro F' _ _ _ k hk q q' a a' hqa hqa' haa
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hk)
      have ha : a.left = a'.left ≫ eA.left := by
        rw [← cancel_mono (genMap u.U), haa, Category.assoc, hgen]
      exact hT F' k hk1 hk q q' a a' hqa hqa' ha)
  have hunit : ∀ w : u.Vˣ, ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V))‖ = 1 := by
    intro w
    have h1 := (u.norm_le (algebraMap u.V _ (w : u.V))).2 ⟨w, rfl⟩
    have h2 := (u.norm_le (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V))‖ *
        ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    have h4 := norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V)))
    have h5 := norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V)))
    nlinarith
  have hpol : ∀ a' b, l.q (s a' + b) - l.q (s a') - l.q b = l.q (a' + m b) - l.q a' - l.q (m b) := by
    intro a' b
    obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord u.V u.D.toPre (s a') b
    obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord u.V u.D.toPre a' (m b)
    obtain ⟨w, hw⟩ := hmain a' b x x' hx hx'
    have n₁ := _root_.GlobalTheory.Poinc.TauNorm.main o Ω S ρ p y₀ u l (s a') b x hx
    have n₂ := _root_.GlobalTheory.Poinc.TauNorm.main o Ω S ρ p y₀ u l a' (m b) x' hx'
    rw [hw, map_mul, norm_mul, hunit, _root_.one_mul, n₂] at n₁
    have := Real.exp_injective n₁
    linarith
  have hpolW : ∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + j χ) - qW W β (fun a => ∑ b, E a b • y b) -
      qW W β (j χ) = qW W β (y + j (m χ)) - qW W β y - qW W β (j (m χ)) := by
    intro y
    have h := hpol (j.symm y) χ
    rw [hq, hq, hq, hq, hq, hq, map_add (f := _), map_add (f := _), hs, AddEquiv.apply_symm_apply, hEm] at h
    have h' : sc * ((qW W β ((fun a => ∑ b, E a b • y b) + j χ) - qW W β (fun a => ∑ b, E a b • y b) -
        qW W β (j χ) : ℤ) : ℝ) = sc * ((qW W β (y + j (m χ)) - qW W β y - qW W β (j (m χ)) : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast mul_left_cancel₀ hsc.ne' h'
  exact GlobalTheory.T.eq_adjoint_apply_of_weightedQuadraticSum_polar W hW X₀ β hβs hβp E E' hEE (j χ) (j (m χ)) hpolW

end GlobalTheory.Poinc.FibMatrix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDimEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.AbVar

theorem isIso_hom_of_dim_eq_zero {K : Type} [Field K] (A : AbVar K) (h : A.dim = 0) : IsIso A.X.hom := by
  have hA := A.ab
  have : IsProper A.X.hom := hA.proper
  have hs : SmoothOfRelativeDimension 0 A.X.hom := h ▸ A.smooth
  have : Etale A.X.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hs
  let e : Sp K ⟶ A.X.left := (1 : 𝟙_ (Over (Sp K)) ⟶ A.X).left
  have he : e ≫ A.X.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over (Sp K)) ⟶ A.X)
  have : IsOpenImmersion e := isOpenImmersion_of_section_of_etale A.X.hom e he
  have : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ A.X.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.X.hom
  obtain ⟨hI, -, -⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  have : ConnectedSpace A.X.left := inferInstance
  have hne : (Set.range e).Nonempty := ⟨_, (default : PrimeSpectrum K), rfl⟩
  have hsurj : Function.Surjective e := Set.range_eq_univ.1
    (IsClopen.eq_univ ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩ hne)
  have : Surjective e := ⟨hsurj⟩
  have : IsIso e := IsOpenImmersion.isIso e
  have : IsIso (e ≫ A.X.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e A.X.hom

theorem hom_eq_of_isIso {K : Type} [Field K] {A : AbVar K} (h : IsIso A.X.hom) {T : Over (Sp K)}
    (g₁ g₂ : T ⟶ A.X) : g₁ = g₂ := by
  ext
  rw [← cancel_mono A.X.hom, Over.w, Over.w]

theorem eq_zero_of_dim_eq_zero :
    ∀ (K : Type) [Field K] (A B : AbVar K), (A.dim = 0 ∨ B.dim = 0) → ∀ f : A ⟶ B, f = 0 := by
  intro K _ A B h f
  rcases h with h | h
  · have hi := isIso_hom_of_dim_eq_zero A h
    apply Subtype.ext
    change f.hom = (0 : A ⟶ B).hom
    rw [zero_hom]
    have e1 : f.hom = (1 : A.X ⟶ A.X) ≫ f.hom := by
      rw [hom_eq_of_isIso hi (1 : A.X ⟶ A.X) (𝟙 A.X), Category.id_comp]
    rw [e1, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  · have hi := isIso_hom_of_dim_eq_zero B h
    apply Subtype.ext
    exact hom_eq_of_isIso hi _ _

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqvDown
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Desc

theorem lawsLL : GlobalTheory.UT.LL :=
  ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1, GlobalTheory.allSixLaws.2.2.2.2.1⟩

theorem eqv_down : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab' E',
    LabExt em lab lab' → Eqv D.toPre A F N lab' E' → ∃ E, Eqv D.toPre A (Kb R) N lab E := by
  intro R _ _ _ hB D A N hN lab F _ _ _ em lab' E' hL hE
  obtain ⟨hAdm, hC⟩ := hB
  have hN1 : 1 ≤ N := hN.pos
  have honto := GlobalTheory.T.torsionLabels_surjective_of_larger_algClosed_field R D.toPre A N hN1 lab F em lab' hL hE.onto
  have hframe : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (p : QkPt D.toPre K N),
      ∃ w, GlobalTheory.UT.TXFrame N p w := fun K _ _ _ p =>
    (GlobalTheory.UT.SymFrame.main lawsLL R (maximalIdeal R) hAdm D K N hN p).1
  let J := {q : (p : QkPt D.toPre (Kb R) N) × GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b ×
      ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R)) // GlobalTheory.UT.TXFrame N q.1 q.2.1 ∧ SymLift A.A A.L N N (lab q.1) q.2.2}
  choose a ha using fun i : J => _root_.GlobalTheory.Mum.PhiLinear.exists_linear_phi R (maximalIdeal R) hAdm D (Kb R) N hN i.1.1 i.1.2.1 i.2.1
  choose b hb using fun i : J => GlobalTheory.T.exists_linearMap_thetaGroup_action_sections R A (Kb R) N i.1.2.2
  have hq := (_root_.GlobalTheory.Mum.qkPt_algClosure_bijective R D.toPre F em N hN1).1
  choose p' hp' using fun i : J => (hq i.1.1).exists
  choose w' hw' using fun i : J => hframe F (p' i)
  have hlab : ∀ i : J, lab' (p' i) = baseEm em ≫ lab i.1.1 := fun i =>
    Over.OverMorphism.ext (by rw [hL _ _ (hp' i)]; rfl)
  choose θ' hθ' using fun i : J =>
    GlobalTheory.WeightProbe.exists_symLift_top A hN (lab' (p' i)) ((hE.onto _).2 ⟨_, rfl⟩)
  choose a' ha' using fun i : J => _root_.GlobalTheory.Mum.PhiLinear.exists_linear_phi R (maximalIdeal R) hAdm D F N hN (p' i) (w' i) (hw' i)
  choose b' hb' using fun i : J => GlobalTheory.T.exists_linearMap_thetaGroup_action_sections R A F N (θ' i)
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  haveI : FiniteDimensional F (Fam D.toPre F N) :=
    (GlobalTheory.UU.finrank_fam_of_laws GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 R D.toPre D.tau_bimult F N hN1).1
  have hfamExt : GlobalTheory.FieldBaseChange.IsExtension (famExt D.toPre em N) :=
    GlobalTheory.FieldBaseChange.isExtension_famPull D.toPre (Kb R) F _ hN1
  have hsecExt := GlobalTheory.T.lineBundlePowSections_algClosure_fieldBaseChange R A F em N
  have ca : ∀ i v, a' i (famExt D.toPre em N v) = famExt D.toPre em N (a i v) := fun i v =>
    ((ha' i _ _).1 (_root_.GlobalTheory.Mum.Desc.phiRel_famExt R (maximalIdeal R) hAdm D F em N hN i.1.1 i.1.2.1 (p' i) (w' i) i.2.1 (hw' i) (hp' i) v _
      ((ha i v _).2 rfl))).symm
  have cb : ∀ i t, b' i (secExt A em N t) = secExt A em N (b i t) := fun i t =>
    ((hb' i _ _).1 (GlobalTheory.T.thetaGroup_symmetricLift_action_fieldExtension R A F em N hN (lab i.1.1) i.1.2.2 (θ' i) i.2.2 (by rw [← hlab i]; exact hθ' i) t _
      ((hb i t _).2 rfl))).symm
  let E'' : Fam D.toPre F N →ₗ[F] SecF A F N :=
    { toFun := E'
      map_add' := fun s t => GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun j =>
        hE.smul c s (c • s) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 rfl) j }
  have cE : ∀ i v, E'' (a' i v) = b' i (E'' v) := fun i v =>
    (hb' i _ _).1 (hE.act (p' i) (w' i) (θ' i) v (a' i v) (hw' i) (hθ' i) ((ha' i v _).2 rfl))
  obtain ⟨E, hEb, hEc⟩ := GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange (Kb R) F _ _ _ _ (famExt D.toPre em N) (secExt A em N) hfamExt hsecExt J a b a' b'
    ca cb E'' hE.bij cE
  refine ⟨fun s => E s, ⟨hEb, ?_, ?_, honto, hframe (Kb R),
    fun p => GlobalTheory.WeightProbe.exists_symLift_top A hN (lab p) ((honto _).2 ⟨p, rfl⟩), ?_⟩⟩
  · intro s s' s'' h j
    have : s'' = s + s' := ReciprocityTheory.ChartRestriction.G.DVR.fam_ext h
    subst this
    exact congrArg (fun q : SecF A (Kb R) N => LB.Sec.f q j) (map_add E s s')
  · intro c s s' h j
    rw [(ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).1 h]
    exact congrArg (fun q : SecF A (Kb R) N => LB.Sec.f q j) (map_smul E c s)
  · intro p w θ s s' hw hθ hP
    let i : J := ⟨⟨p, w, θ⟩, hw, hθ⟩
    have e1 : s' = a i s := (ha i s s').1 hP
    have e2 : E s' = b i (E s) := by rw [e1]; exact hEc i s
    exact (hb i (E s) (E s')).2 e2

end GlobalTheory.Mum.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPowMulMemHermPairSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.ExtPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem compactSpace_of_projOver {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace Y := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem unitAt_zpow {z : X} {u : X.functionField} (h : UnitAt z u) (n : ℤ) : UnitAt z (u ^ n) := by
  have hu : u ≠ 0 := h.ne_zero
  induction n using Int.induction_on with
  | zero => rw [zpow_zero]; exact unitAt_one z
  | succ n ih => rw [zpow_add_one₀ hu]; exact ih.mul h
  | pred n ih => rw [zpow_sub_one₀ hu]; exact ih.mul h.inv

theorem loc_change (P : Pair p) (a b : ℤ) (f : X.functionField) (i i' : P.L.B.ι) (j j' : P.A.B.ι) :
    P.loc a b f i' j' = P.loc a b f i j *
      (((P.r i' : X.functionField) / P.r i) ^ a * ((P.r' j' : X.functionField) / P.r' j) ^ b) := by
  have h1 : (P.r i : X.functionField) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : (P.r' j : X.functionField) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc, div_zpow]
  field_simp

theorem unitAt_quot (P : Pair p) (a b : ℤ) {z : X} {i i' : P.L.B.ι} {j j' : P.A.B.ι}
    (hi : z ∈ P.L.B.U i) (hi' : z ∈ P.L.B.U i') (hj : z ∈ P.A.B.U j) (hj' : z ∈ P.A.B.U j') :
    UnitAt z (((P.r i' : X.functionField) / P.r i) ^ a * ((P.r' j' : X.functionField) / P.r' j) ^ b) :=
  (unitAt_zpow (germOf_eq_iff.1 (P.hr.germOf_eq hi' hi)) a).mul
    (unitAt_zpow (germOf_eq_iff.1 (P.hr'.germOf_eq hj' hj)) b)

theorem loc_pow_mul (P : Pair p) (e a b : ℤ) (c : ℕ) (x f : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (e * c + a) b (x ^ c * f) i j = P.loc e 0 x i j ^ c * P.loc a b f i j := by
  have h0 : (P.r i : X.functionField) ≠ 0 := Units.ne_zero _
  simp only [Pair.loc, zpow_zero, mul_one, zpow_add₀ h0, zpow_mul, zpow_natCast, mul_pow]
  ring

theorem exists_pow_mul_regAt {W : X.Opens} (hW : IsAffineOpen W) (s : Γ(X, W)) (hg : genericPoint X ∈ X.basicOpen s)
    {g : X.functionField} (h : ∀ z ∈ X.basicOpen s, RegAt z g) :
    ∃ N : ℕ, ∀ z ∈ W, RegAt z (fnOf W (X.basicOpen_le s hg) s ^ N * g) := by
  obtain ⟨a, ha⟩ := exists_fnOf_eq hg h
  have := hW.isLocalization_basicOpen s
  obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) a
  obtain ⟨N, hN⟩ := m.2
  refine ⟨N, fun z hz => ?_⟩
  have e := congrArg (fnOf _ hg) hm
  simp only [map_mul] at e
  change fnOf _ hg a * fnOf _ hg (resG X (X.basicOpen_le s) (m : Γ(X, W))) =
    fnOf _ hg (resG X (X.basicOpen_le s) b) at e
  rw [fnOf_resG, fnOf_resG, ha, ← hN, map_pow] at e
  rw [mul_comm, e]
  exact regAt_fnOf hz _ b

end GlobalTheory.HSAmp.ExtPow


open GlobalTheory.HSAmp.ExtPow in
theorem GlobalTheory.HSAmp.eventually_pow_mul_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e a b : ℤ) (x f : X.functionField), x ∈ P.H e 0 → x ≠ 0 → (∀ z ∈ NV P e 0 x, ∀ i j, z ∈ P.L.B.U i → z ∈ P.A.B.U j → RegAt z (P.loc a b f i j)) → ∀ᶠ c : ℕ in atTop, x ^ c * f ∈ P.H (e * c + a) b := by
  intro k _ X _ p D hD P e a b x f hx hx0 hf
  haveI : CompactSpace X := compactSpace_of_projOver hD.isProjOver
  have loc_ok : ∀ z : X, ∃ W : X.Opens, z ∈ W ∧ ∃ N : ℕ, ∀ c : ℕ, N ≤ c → ∀ w ∈ W, ∀ i j, w ∈ P.L.B.U i →
      w ∈ P.A.B.U j → RegAt w (P.loc (e * c + a) b (x ^ c * f) i j) := by
    intro z
    obtain ⟨i, hi⟩ := exists_chart P.L.isLB z
    obtain ⟨j, hj⟩ := exists_chart P.A.isLB z
    obtain ⟨W, hW, hzW, hWle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show z ∈ P.L.B.U i ⊓ P.A.B.U j from ⟨hi, hj⟩)
    have hgW : genericPoint X ∈ W := gen_mem hzW
    have hsW : ∀ w ∈ W, RegAt w (P.loc e 0 x i j) := fun w hw => hx w i j (hWle hw).1 (hWle hw).2
    obtain ⟨s, hs⟩ := exists_fnOf_eq hgW hsW
    have hbas : ∀ w ∈ X.basicOpen s, w ∈ NV P e 0 x := by
      intro w hw i' j' hi' hj'
      have hwW := X.basicOpen_le s hw
      have hu : UnitAt w (P.loc e 0 x i j) := hs ▸ (unitAt_fnOf_iff hwW hgW s).2 hw
      rw [loc_change P e 0 x i i' j j']
      exact hu.mul (unitAt_quot P e 0 (hWle hwW).1 hi' (hWle hwW).2 hj')
    have hne : P.loc e 0 x i j ≠ 0 :=
      mul_ne_zero (mul_ne_zero hx0 (zpow_ne_zero _ (Units.ne_zero _))) (zpow_ne_zero _ (Units.ne_zero _))
    have hg0 : genericPoint X ∈ X.basicOpen s := by
      have hu : UnitAt (genericPoint X) (fnOf W hgW s) := by rw [hs]; exact unitAt_genericPoint hne
      exact (unitAt_fnOf_iff hgW hgW s).1 hu
    obtain ⟨N, hN⟩ := exists_pow_mul_regAt hW s hg0 (g := P.loc a b f i j) fun w hw =>
      hf w (hbas w hw) i j (hWle (X.basicOpen_le s hw)).1 (hWle (X.basicOpen_le s hw)).2
    refine ⟨W, hzW, N, fun c hc w hw i' j' hi' hj' => ?_⟩
    rw [loc_change P (e * c + a) b (x ^ c * f) i i' j j', loc_pow_mul, ← hs]
    refine RegAt.mul ?_ (unitAt_quot P _ b (hWle hw).1 hi' (hWle hw).2 hj').regAt
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
    have hd := regAt_fnOf hw hgW (s ^ d)
    rw [map_pow] at hd
    rw [pow_add, mul_comm (_ ^ N) (_ ^ d), mul_assoc]
    exact hd.mul (hN w hw)
  choose W hzW N hN using loc_ok
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun z => (W z : Set X)) (fun z => (W z).isOpen)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hzW z⟩)
  refine eventually_atTop.2 ⟨t.sup N, fun c hc w i j hi hj => ?_⟩
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ w))
  exact hN z c ((Finset.le_sup hz).trans hc) w hwz i j hi hj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySurjectiveToPushforwardAmpleLineBundle
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

noncomputable section
namespace GlobalTheory.SerreOnto
open CategoryTheory.Limits

variable {X T : Scheme.{0}} (i : T ⟶ X)

def unitToPush : GlobalTheory.LB.unitMod X ⟶ (Scheme.Modules.pushforward i).obj (GlobalTheory.LB.unitMod T) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

theorem toPushforward_comp (M : LB X) :
    GlobalTheory.LB.toPushforward M i ≫ ((Scheme.Modules.pushforward i).map (Twist.unitTwistIso (M.pull i)).inv ≫
      (Twist.projIso M i (GlobalTheory.LB.unitMod T)).hom) =
      (Twist.unitTwistIso M).inv ≫ Twist.map M (unitToPush i) := by
  apply Twist.hom_ext
  intro V s j
  change resG T (Twist.le_pull_inf i V j)
      ((i.appLE _ _ (GlobalTheory.LB.pull_inf_le i V (fun _ => j))).hom (GlobalTheory.LB.coord s j)) =
    (i.app _).hom (GlobalTheory.LB.coord s j)
  rw [GlobalTheory.LB.resG_appLE, ← Scheme.Hom.appLE_eq_app]

def kernelIso (M : LB X) (hM : M.IsLB) :
    kernel (GlobalTheory.LB.toPushforward M i) ≅ twist (kernel (unitToPush i)) M :=
  haveI := Twist.preservesFiniteLimits_twistFunctor hM
  kernel.mapIso _ _ (Twist.unitTwistIso M).symm
    ((Scheme.Modules.pushforward i).mapIso (Twist.unitTwistIso (M.pull i)).symm ≪≫
      Twist.projIso M i _) (toPushforward_comp i M) ≪≫
    (PreservesKernel.iso (twistFunctor M) (unitToPush i)).symm

end GlobalTheory.SerreOnto


open CategoryTheory.Limits in
theorem GlobalTheory.surjective_toPushforward_app_top_lbPow : ∀ (k : Type) [CommRing k] [IsNoetherianRing k]
    (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : LB X), IsAmpleLB L →
    ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i], ∀ᶠ N in atTop,
      Function.Surjective ((GlobalTheory.LB.toPushforward (lbPow L N) i).app ⊤) := by
  intro k _ _ X p hp L hL T i _
  letI : Algebra k Γ(X, ⊤) := (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have hf : ∀ r, algebraMap k Γ(X, ⊤) r = p.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom r) :=
    fun _ => rfl
  haveI := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : QCoh.IsFiniteQC (kernel (GlobalTheory.SerreOnto.unitToPush i)) :=
    QCoh.IsFiniteQC.of_mono (kernel.ι (GlobalTheory.SerreOnto.unitToPush i))
  filter_upwards [hL.eventually_subsingleton_coh_twist hf (kernel (GlobalTheory.SerreOnto.unitToPush i))]
    with N hN
  have hM : (lbPow L N).IsLB := isLB_lbPow hL.isLB N
  haveI := GlobalTheory.PinchLift.epi_toPushforward_of_closedImm i hM
  let φ := GlobalTheory.LB.toPushforward (lbPow L N) i
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (S.exact_of_f_is_kernel (kernelIsKernel φ)) inferInstance inferInstance
  refine cohOn.app_surjective hS ⊤ ?_
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ 1 (GlobalTheory.SerreOnto.kernelIso i _ hM)).toEquiv.subsingleton_congr.2
    (hN 1 one_pos)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveSectionValueUnitFrame
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.ValAdd

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem ratVal_add' {σ : k →+* ℂ} {y : CxPts p σ} {f g : X.functionField} (hf : RegAt (under y) f)
    (hg : RegAt (under y) g) : ratVal (f + g) y = ratVal f y + ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn p σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_add,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_add]

theorem val_add (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) {f g : X.functionField}
    (hf : f ∈ P.H a b) (hg : g ∈ P.H a b) : val P a b σ y (f + g) = val P a b σ y f + val P a b σ y g := by
  have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
  have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
  have e : P.loc a b (f + g) (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) =
      P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) +
        P.loc a b g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]; ring
  rw [val, val, val, e, ratVal_add' (hf _ _ _ hi hj) (hg _ _ _ hi hj), add_mul]

end GlobalTheory.HSAmp.ValAdd


open GlobalTheory.HSAmp.ValAdd in
theorem GlobalTheory.HSAmp.val_additive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ ℓ : P.H a b →+ ℂ, ∀ f : P.H a b, ℓ f = val P a b σ y f := by
  intro k _ X _ p P a b σ y
  refine ⟨{ toFun := fun f => val P a b σ y f, map_zero' := ?_, map_add' := fun f g => val_add P a b σ y f.2 g.2 }, fun _ => rfl⟩
  have := val_add P a b σ y (zero_mem (P.H a b)) (zero_mem (P.H a b))
  simp only [add_zero] at this
  simpa using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesSemilinearPDivGroupHomChaStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G), ∃! φ : Fin d → MvPowerSeries (Fin e) k', ∀ n j, c'.ev n (φ j) = s.app n (c.x n j) := by
  first | (exact @GlobalTheory.Katz.existsUnique_semiHom_ev) | (exact GlobalTheory.Katz.existsUnique_semiHom_ev) | (intros; apply GlobalTheory.Katz.existsUnique_semiHom_ev  <;> assumption)
end

