module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionSectionsOfRoot
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameReadingLeadingMinorProductExtremal
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel
section
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory


open scoped TensorProduct in
theorem natCard_quot_smul_top_of_projective {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  classical
  open scoped TensorProduct in
  have hA : Finite (Ideal (R ⧸ I)) :=
    Finite.of_injective (fun J : Ideal (R ⧸ I) => (J : Set (R ⧸ I))) SetLike.coe_injective
  have hMS : Finite (MaximalSpectrum (R ⧸ I)) :=
    Finite.of_injective (fun m : MaximalSpectrum (R ⧸ I) => m.asIdeal) (fun a b h => MaximalSpectrum.ext h)
  have rk : ∀ P : MaximalSpectrum (R ⧸ I), Module.finrank ((R ⧸ I) ⧸ P.1)
      (((R ⧸ I) ⧸ P.1) ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] N)) = Module.finrank R N := by
    intro P
    have hP := P.2
    let _ : Field ((R ⧸ I) ⧸ P.1) := Ideal.Quotient.field P.1
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.1) ((R ⧸ I) ⧸ P.1) N).finrank_eq]
    have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := (R ⧸ I) ⧸ P.1)
      (M := ((R ⧸ I) ⧸ P.1) ⊗[R] N)) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_baseChange, Pi.natCast_apply, Nat.cast_id] at h1
    rw [← h1]
    generalize PrimeSpectrum.comap (algebraMap R ((R ⧸ I) ⧸ P.1)) ⟨⊥, Ideal.isPrime_bot⟩ = q
    obtain ⟨p, hp⟩ := q
    rw [← Ideal.finrank_fiber_eq_rankAtStalk, Ideal.finrank_fiber_eq_finrank]
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N)
    (Module.finrank R N) rk
  calc Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card ((R ⧸ I) ⊗[R] N) :=
        Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv.symm
    _ = Nat.card (Fin (Module.finrank R N) → R ⧸ I) := Nat.card_congr b.equivFun.toEquiv
    _ = Nat.card (R ⧸ I) ^ Module.finrank R N := by simp [Nat.card_fun]

theorem absNorm_level_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    Ideal.absNorm l.Mb = l.M ^ FD.fdeg E := by
  have h1 : Ideal.absNorm (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm l.Mb := by
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv l.Mb _ H.bar rfl).toEquiv.symm
  have h2 := congrArg Ideal.absNorm l.prod
  rw [map_mul, h1, Ideal.absNorm_span_singleton] at h2
  have h3 : (Algebra.norm ℤ ((l.M : ℕ) : 𝓞 E)).natAbs = l.M ^ Module.finrank ℚ E := by
    have : ((l.M : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (l.M : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hev : Module.finrank ℚ E = 2 * FD.fdeg E := by
    have h := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h
    unfold FD.fdeg
    omega
  rw [h3, hev, pow_mul', ← sq] at h2
  exact Nat.pow_left_injective two_ne_zero h2

theorem card_levQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H),
    Finite (LevQ Dw l) ∧ Nat.card (LevQ Dw l) = l.M ^ (FD.fdeg E * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l
  unfold LevQ
  have := Dw.fin
  have := Dw.proj
  have hN := absNorm_level_half l
  have : Finite (𝓞 E ⧸ l.Mb) := by
    rw [← Ideal.absNorm_ne_zero_iff, hN]
    exact pow_ne_zero _ (by have := l.three_le; omega)
  have hc := natCard_quot_smul_top_of_projective (N := Dw.La) l.Mb
  have hq : Nat.card (𝓞 E ⧸ l.Mb) = l.M ^ FD.fdeg E := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Dw.rank, hq, ← pow_mul] at hc
  refine ⟨?_, hc⟩
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  exact pow_ne_zero _ (by have := l.three_le; omega)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBiextensionChartWithGermsFramedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.ChartRing

theorem bijective_appTop_powObj (hGF : GlobalFnsSt) {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (hG : IsAbelianScheme G) (n : ℕ) :
    Function.Bijective (ReciprocityTheory.ChartRestriction.G.Out.powObj G n).hom.appTop.hom := by
  cases n with
  | zero =>
    show Function.Bijective (𝟙 S : S ⟶ S).appTop.hom
    simp only [Scheme.Hom.id_appTop, CommRingCat.hom_id]
    exact Function.bijective_id
  | succ n => exact hGF _ _ (AbelianSchemeGerms.isAbelianScheme_powObj G hG n)


set_option maxHeartbeats 1600000 in
theorem exists_chartAt_with_germs : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S), ∃ C : ChartAt Xo c y, FrTruncC y C ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f := by
  intro hL E _ _ _ H Dw l Xo c _ hstar S _ _ _ y
  obtain ⟨d, G, A, uvec, x, -, -, hchG⟩ :=
    GlobalTheory.ChartData.exists_isChartG_of_basis E H Xo.X Xo.univ.t S y.x (Lt1 Dw) (fun ℓ => y.u ℓ.1 ℓ.2)
      (fun ℓ => y.tan ℓ.1 ℓ.2) (fun w hw => GlobalTheory.FrameTangent.frame_tangent_basis E H Dw l Xo c S y w hw)
  have hch := (isChart_iff y d G.F A.act uvec x).2 hchG
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, hpr, htr, hfa, had, hrig⟩ :=
    GlobalTheory.exists_frames_of_chart E H Xo.X Xo.univ.t S y.x d G A (Lt1 Dw) _ uvec x hchG
  have hPow := bijective_appTop_powObj hL.globalFns Xo.univ.t.G (GlobalTheory.moduli_univ_polAV E H Dw l Xo).2.2.2.1
  obtain ⟨hax, hr⟩ := GlobalTheory.FrameBiextId.fbId E H Xo.X Xo.univ.t hPow hstar S y.x d G A (Lt1 Dw) _ uvec x e
    ph1 ph2 sy ad hchG hfr hfa had
  obtain ⟨h, hh⟩ := GlobalTheory.canonGauge_exists S d (𝓞 E) S (mkFB G A ph1 ph2 sy ad hax hr)
  refine ⟨⟨d, mkFB G A ph1 ph2 sy ad hax hr, uvec, x, e, wP, h, hch,
    (isFrame_iff y d x _ _ _ _ _ _ e).2 hfr, (isPrim_iff wP).2 hpr, hh, hrig⟩, htr, ?_⟩
  intro k F
  obtain ⟨f, hf⟩ := germSt_holds E H Xo.X Xo.univ.t S y.x d G.F A.act (Lt1 Dw) _ uvec x ph1 ph2 sy ad e wP
    hchG hfr hpr htr k F
  exact ⟨f, (isGerm_iff y d x _ e wP k F f).2 hf⟩

end GlobalTheory.ChartRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsIdempotentElemRangeSpMapSubset
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem eq_one_iff_isUnit_of_isIdempotentElem {R : Type} [CommRing R] {u : R} (hu : IsIdempotentElem u) :
    u = 1 ↔ IsUnit u := by
  constructor
  · rintro rfl
    exact isUnit_one
  · intro h
    exact h.mul_left_cancel (by rw [hu.eq, _root_.mul_one])

private theorem isUnit_iff_forall_primeSpectrum_notMem {R : Type} [CommRing R] (x : R) :
    IsUnit x ↔ ∀ q : PrimeSpectrum R, x ∉ q.asIdeal := by
  constructor
  · intro h q hq
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq h)
  · intro h
    by_contra hx
    obtain ⟨I, hI, hxI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
    exact h ⟨I, hI.isPrime⟩ hxI

theorem exists_isIdempotentElem_range_spMap_subset {B : Type} [CommRing B] {U : Set (Sp B)} (hU : IsClopen U) :
    ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T), χ e = 1 ↔ Set.range (spMap χ) ⊆ U := by
  let s : TopologicalSpace.Clopens (PrimeSpectrum B) := ⟨U, hU⟩
  have he : IsIdempotentElem (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).1 :=
    (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).2

  have hmem : ∀ p : PrimeSpectrum B,
      p ∈ U ↔ (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).1 ∉ p.asIdeal := by
    intro p
    have h := congrArg (fun o : TopologicalSpace.Opens (PrimeSpectrum B) => p ∈ o)
      (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm s)
    simp only [eq_iff_iff] at h
    rw [PrimeSpectrum.mem_basicOpen] at h
    exact h.symm
  refine ⟨_, he, fun T _ χ => ?_⟩
  rw [eq_one_iff_isUnit_of_isIdempotentElem (he.map χ), isUnit_iff_forall_primeSpectrum_notMem]
  constructor
  · rintro h _ ⟨q, rfl⟩
    exact (hmem _).2 (h q)
  · intro h q
    exact (hmem _).1 (h ⟨q, rfl⟩)

theorem exists_isIdempotentElem_torsion_eq :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (k : ℕ), 0 < k → ∀ (a b : ptO Xo x0 ⟶ Xo.univ.t.G), a ^ k = 1 → b ^ k = 1 → ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T), χ e = 1 ↔ spMap χ ≫ a.left = spMap χ ≫ b.left := by
  intro _ E _ _ _ H Dw l Xo B _ x0 k hk a b ha hb
  obtain ⟨-, -, hunit, hab, -⟩ := moduli_univ_polAV E H Dw l Xo
  obtain ⟨Z, et, hZf, hZe, hadd, hpow, huniv⟩ :=
    exists_finiteEtale_latticeTorsionHom Xo.X Xo.univ.t.G k ℤ hab (hunit k hk)
  have R : LevCover.RepTors Xo.univ.t.G k ℤ Z et := ⟨hZf, hZe, hadd, hpow, huniv⟩

  have hz : ∀ c : ptO Xo x0 ⟶ Xo.univ.t.G, c ^ k = 1 → ∀ m : ℤ, (c ^ m) ^ k = 1 := by
    intro c hc m
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]
  obtain ⟨U, hUc, hU⟩ := R.clopenCond (T := ptO Xo x0) (fun m => a ^ m) (fun m => b ^ m)
    (fun m c => zpow_add a m c) (hz a ha) (fun m c => zpow_add b m c) (hz b hb)
  let V : Set (Sp B) := (U : Set (ptO Xo x0).left)
  obtain ⟨e, he, hE⟩ := exists_isIdempotentElem_range_spMap_subset (B := B) (U := V) ⟨hUc, U.isOpen⟩
  refine ⟨e, he, fun T _ χ => ?_⟩
  rw [hE T χ]
  let h : Over.mk (spMap χ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap χ) rfl
  have hh : Set.range (spMap χ) ⊆ V ↔ Set.range h.left ⊆ U := Iff.rfl
  rw [hh, ← hU _ h]
  simp only [GrpObj.comp_zpow]
  constructor
  · intro hm
    have h1 : h ≫ a = h ≫ b := by simpa using hm 1
    simpa [h] using congrArg CommaMorphism.left h1
  · intro hl m
    have h1 : h ≫ a = h ≫ b := Over.OverMorphism.ext (by simpa [h] using hl)
    rw [h1]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.PrimRd

theorem finset_fin_two_eq_cases (I : Finset (Fin 2)) : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  revert I
  decide

theorem e_psum {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (w : A ⟶ A) (z z' : Fin g → ℂ) (h : Φ.e z' = Φ.e z ≫ w) (I : ULift.{0} (Finset (Fin 2))) :
    Φ.e z ≫ psum A ![𝟙 A, w] I.down = Φ.e (psumL 2 g I ![z, z']) := by
  obtain ⟨I⟩ := I
  have h0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  rcases finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl
  · show Φ.e z ≫ (toUnit A ≫ η) = _
    simp [psumL, h0]
    rfl
  · show Φ.e z ≫ (lift (𝟙 A) (toUnit A ≫ η) ≫ μ) = _
    simp [psumL]
  · show Φ.e z ≫ (lift w (toUnit A ≫ η) ≫ μ) = _
    simp [psumL]
    exact h.symm
  · show Φ.e z ≫ (lift (𝟙 A) (lift w (toUnit A ≫ η) ≫ μ) ≫ μ) = _
    simp [psumL, Φ.e_add, h]
    rw [← Category.assoc, comp_lift, Category.comp_id]
    rfl

theorem sum_ulift_finset_fin_two_expand {M : Type} [AddCommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∑ I, f I = f ⟨∅⟩ + f ⟨{0}⟩ + f ⟨{1}⟩ + f ⟨{0, 1}⟩ := by
  rw [Fintype.sum_equiv Equiv.ulift f (fun x => f ⟨x⟩) (fun _ => rfl)]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [add_assoc]

theorem sameSum_of_const {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (f : Y ⟶ X) (h : ∀ k, φ k = f) (h' : ∀ k, φ' k = f)
    (hs : ∑ k, ε k = ∑ k, ε' k) : LB.SameSum φ ε φ' ε' := by
  intro ψ
  by_cases hψ : f = ψ
  · subst hψ
    simpa [h, h'] using hs
  · simp [h, h', hψ]

private theorem w0_add_bar_w0_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hrt : H.bar H.rt = -H.rt := by
    apply RingOfIntegers.ext
    rw [H.bar_eq]
    push_cast
    set r : E := (H.rt : E) with hr
    have hr2 : r ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa [hr] using this
    have hc2 : (IsCMField.complexConj E r) ^ 2 = r ^ 2 := by
      rw [← map_pow, hr2]
      simp
    have hprod : (IsCMField.complexConj E r - r) * (IsCMField.complexConj E r + r) = 0 := by
      linear_combination hc2
    rcases mul_eq_zero.1 hprod with h1 | h1
    · exfalso
      have heq : IsCMField.complexConj E r = r := sub_eq_zero.1 h1
      let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
      have h3 := IsCMField.complexEmbedding_complexConj E τ r
      rw [heq] at h3
      have him : (τ r).im = 0 := by
        have := congrArg Complex.im h3
        simp at this
        linarith
      have h4 : (τ r) ^ 2 = -(H.d : ℂ) := by
        rw [← map_pow, hr2]
        simp
      have h5 : τ r = ((τ r).re : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [h5] at h4
      have h6 : (τ r).re ^ 2 = -(H.d : ℝ) := by exact_mod_cast h4
      have h7 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
      nlinarith [sq_nonneg (τ r).re]
    · exact eq_neg_of_add_eq_zero_left h1
  have hb : H.bar (2 * H.w0) = H.bar (1 + H.rt) := by rw [H.two_weight_eq_one_add_root]
  rw [map_mul, map_add (f := _), map_one, hrt, map_ofNat] at hb
  have h2 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    linear_combination H.two_weight_eq_one_add_root + hb
  exact mul_left_cancel₀ two_ne_zero h2

private theorem hf_eq_cj_hf_swap_of_isHerm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (T Tb : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hadj : ∀ z w, hermForm Hm (T z) w = hermForm Hm z (Tb w)) (hTT : ∀ w, T w + Tb w = w) (z w : Fin g → ℂ) :
    ∑ k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)), (((Sum.elim (fun _ => (1 : ℤ)) fun I => -cε 2 I) k : ℤ) : ℂ) *
      hermForm Hm ((Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, T])) :
        (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k z)
        ((Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, T])) :
        (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k w) = 0 := by
  have hB1 : ∀ a b c, hermForm Hm (a + b) c = hermForm Hm a c + hermForm Hm b c := by
    intro a b c
    simp [hermForm, add_dotProduct]
  have hB2 : ∀ a b c, hermForm Hm a (b + c) = hermForm Hm a b + hermForm Hm a c := by
    intro a b c
    simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  have hB0 : ∀ a, hermForm Hm 0 a = 0 := by intro a; simp [hermForm]
  rw [Fintype.sum_sum_type, sum_ulift_finset_fin_two_expand, Fin.sum_univ_one]
  simp [psumL, cε, hB1, hB2, hB0]
  have k3 : hermForm Hm z w = hermForm Hm z (T w) + hermForm Hm z (Tb w) := by rw [← hB2, hTT]
  rw [hadj z w]
  linear_combination k3

theorem prim_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∃ wP : PrimTy H Xo, IsPrim wP) ∧ ∀ wP : PrimTy H Xo, IsPrim wP → ∀ z : Fin g → ℂ, Φ.toAnFr.GenRd _ _ wP (Φ.e z).left (Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z])) 1 := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ
  have hw0 : IsMonHom (Xo.univ.t.act.act H.w0) := Xo.univ.t.act.hom H.w0
  have hη : η ≫ Xo.univ.t.act.act H.w0 = η := IsMonHom.one_hom _
  refine ⟨Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_wP Xo.univ.t, ?_⟩
  intro wP hP z
  obtain ⟨hPg, hPc⟩ := hP
  let Λ : (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    Sum.elim (fun _ => LinearMap.id)
      (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, tyAct ty H.w0]))
  have hΛl : ∀ k z, Λ (Sum.inl k) z = z := fun _ _ => rfl
  have hΛr : ∀ I z, Λ (Sum.inr I) z = psumL 2 g I ![z, tyAct ty H.w0 z] := by
    intro I z
    simp only [Λ, Sum.elim_inr, LinearMap.comp_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hlin : ∀ z, Φ.e (tyAct ty H.w0 z) = Φ.e z ≫ Xo.univ.t.act.act H.w0 := Φ.lin H.w0
  have h0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  have hφ : ∀ z k, (Φ.e z).left ≫
      (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k =
      (Φ.e (Λ k z)).left := by
    intro z k
    rcases k with k | I
    · simp [hΛl]
    · have := e_psum Φ.toAnFr (Xo.univ.t.act.act H.w0) z (tyAct ty H.w0 z) (hlin z) I
      rw [hΛr, ← this]
      rfl
  have hT : ∀ gm ∈ Φ.lat, tyAct ty H.w0 gm ∈ Φ.lat := by
    intro gm hgm
    apply (Φ.e_ker _).1
    rw [hlin, (Φ.e_ker gm).2 hgm]
    show (toUnit _ ≫ η) ≫ _ = toUnit _ ≫ η
    rw [Category.assoc, hη]
  have p0 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨∅⟩ ![a, b] = 0 := by intro a b; simp [psumL]
  have p1 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{0}⟩ ![a, b] = a := by intro a b; simp [psumL]
  have p2 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{1}⟩ ![a, b] = b := by intro a b; simp [psumL]
  have p3 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{0, 1}⟩ ![a, b] = a + b := by intro a b; simp [psumL]
  have hper : ∀ gm ∈ Φ.lat, (∀ z, (Φ.e (z + gm)).left = (Φ.e z).left) ∧ ∀ k, Λ k gm ∈ Φ.lat := by
    intro gm hgm
    refine ⟨fun z => by rw [Φ.e_add, (Φ.e_ker gm).2 hgm, _root_.mul_one], fun k => ?_⟩
    rcases k with k | I
    · exact hgm
    · rw [hΛr]
      obtain ⟨I⟩ := I
      rcases finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl
      · rw [p0]
        exact zero_mem _
      · rw [p1]
        exact hgm
      · rw [p2]
        exact hT gm hgm
      · rw [p3]
        exact add_mem hgm (hT gm hgm)
  have hbar := w0_add_bar_w0_eq_one H
  have hTT : ∀ w, tyAct ty H.w0 w + tyAct ty (H.bar H.w0) w = w := by
    intro w
    funext k
    have h1 : ((H.w0 : E) + (H.bar H.w0 : E)) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) hbar
    simp only [tyAct, Pi.add_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [← add_mul, ← map_add (f := _), h1, map_one, _root_.one_mul]
  have hherm : ∀ z w, ∑ k, (((Sum.elim (fun _ => (1 : ℤ)) fun I => -cε 2 I) k : ℤ) : ℂ) *
      hermForm Φ.Hm (Λ k z) (Λ k w) = 0 :=
    fun z w => hf_eq_cj_hf_swap_of_isHerm Φ.Hm (tyAct ty H.w0) (tyAct ty (H.bar H.w0)) (Φ.adj H.w0) hTT z w
  obtain ⟨⟨v, hv0, hv⟩, -⟩ := _root_.GlobalTheory.AnVal.genRd_const _ _ _ _ g Φ.toAnFr _ _
    (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0]))
    (Sum.elim (fun _ => 1) fun I => -cε 2 I) wP hPg g (fun z => (Φ.e z).left) Λ Φ.lat Φ.hol hφ Φ.span hper hherm
  have heS : ∀ k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)), eSec Xo.univ.t.G ≫
      (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k =
      eSec Xo.univ.t.G := by
    intro k
    rcases k with k | I
    · simp
    · obtain ⟨I⟩ := I
      show (η ≫ psum Xo.univ.t.G ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0] I).left = (η : _ ⟶ Xo.univ.t.G).left
      congr 1
      rcases finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl
      · show η ≫ (toUnit _ ≫ η) = η
        simp
      · show η ≫ (lift (𝟙 _) (toUnit _ ≫ η) ≫ μ) = η
        simp
      · show η ≫ (lift (Xo.univ.t.act.act H.w0) (toUnit _ ≫ η) ≫ μ) = η
        simp [hη]
      · show η ≫ (lift (𝟙 _) (lift (Xo.univ.t.act.act H.w0) (toUnit _ ≫ η) ≫ μ) ≫ μ) = η
        simp
  have hv1 : v = 1 := by
    have A0 := hv 0
    have hz : ∀ k, Λ k 0 = 0 := fun k => map_zero _
    have hq0 : (Φ.e 0).left = y.x ≫ eSec Xo.univ.t.G := by
      rw [h0]
      rfl
    simp only [hz, hq0] at A0
    have A2 := ((GlobalTheory.T.generatorReading_pullback_period_rigid _ _ _ _ g Φ.toAnFr _ _ _ _ wP).1 _ (eSec Xo.univ.t.G) y.x _ v).2 A0
    have A3 : Φ.toAnFr.GenRd (fun _ : PUnit => eSec Xo.univ.t.G) (fun _ => 1) Xo.univ.t.PP.rig y.x (fun _ => 0) 1 := by
      obtain ⟨b1, b2⟩ := (GlobalTheory.T.generatorReading_pullback_period_rigid _ _ _ _ g Φ.toAnFr _ _
        (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0]))
        (Sum.elim (fun _ => 1) fun I => -cε 2 I) wP).2.2 1
      refine ⟨b1, fun j hj => ?_⟩
      have b3 := b2 j hj
      simpa [rigPow] using b3
    have hsame : LB.SameSum (fun k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) => eSec Xo.univ.t.G ≫
        (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k)
        (Sum.elim (fun _ => 1) fun I => -cε 2 I) (fun _ : PUnit => eSec Xo.univ.t.G) (fun _ => 1) := by
      refine sameSum_of_const (eSec Xo.univ.t.G) heS (fun _ => rfl) ?_
      rw [Fintype.sum_sum_type, sum_ulift_finset_fin_two_expand, Fin.sum_univ_one]
      simp [cε]
    exact (_root_.GlobalTheory.AnValGenCorr.genRd_corr_mul_inv _ _ _ _ g Φ.toAnFr _ _ _ _ _ _ _ _ _ y.x _ _ v 1 A2 A3).2.1 hPc hsame
      ⟨fun _ => 0, fun _ => rfl, fun _ => rfl⟩
  have hfin := hv z
  rw [hv1] at hfin
  have hpt : (fun k => Λ k z) = Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z]) := by
    funext k
    rcases k with k | I
    · rfl
    · exact hΛr I z
  rw [hpt] at hfin
  exact hfin

end GlobalTheory.AnVal.PrimRd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameReadingLeadingMinorProductExtremalStatement
section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameReading_leadingMinorProduct_extremal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → ∃ ε : ℤˣ, cof Dw pl c.F n (pG (Dw := Dw) c a n) = ((ε : ℤ) : c.F) • (detFac Dw pl c.F a s lam * ten fun t => extremal c.F n (lam t)) := by
  first | exact @GlobalTheory.FrameReadHw.cof_pG | exact GlobalTheory.FrameReadHw.cof_pG | (intros; apply GlobalTheory.FrameReadHw.cof_pG <;> assumption)
end

