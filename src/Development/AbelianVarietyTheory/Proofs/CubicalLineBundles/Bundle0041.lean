module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOrthonormalFrameBorelChangeComplexFramedPo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem lact_one_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (y : FD.Frame Ψ r) : FD.lact (1 : GL (Fin r) E) y = y := by
  funext τ
  simp [FD.lact, FD.mat]
  rfl

theorem exists_ortho_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), (U.X k).IsOrtho x.1 ∧ FrBor t (U.un k x) y := by
  intro E _ _ _ H Dw l Xo c σ r U hU y
  obtain ⟨-, -, h3, h4, -⟩ := hU
  obtain ⟨k, x, t, ht⟩ := h3 y
  obtain ⟨b, hb, ho⟩ := (FD.orthonormalFlagTranslate_holds r (U.X k)).1 x.1 x.2
  have hd := FD.OrthogonalFrameDomain.rmul_mem_dom (U.X k) x.2 hb
  obtain ⟨t', ht'⟩ := (h4 k k x ⟨_, hd⟩).2 ⟨1, (U.X k).Γ.one_mem, b, hb, by rw [lact_one_frame]⟩
  have hi := (frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) (U.un k ⟨_, hd⟩) y).2.2.2 t' ht'
  exact ⟨k, ⟨_, hd⟩, t * t'⁻¹, ho,
    (frBor_calculus E H Dw l Xo c (CAt σ) (U.un k ⟨_, hd⟩) (U.un k x) y).2.2.1 _ _ hi ht⟩

end GlobalTheory.LamT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfPolAV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LamF

theorem exists_pat_of_polAV : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → ∃ (T : PAT H (Sp R)) (e : T.t.G ≅ P.A), T.g = P.g ∧ Serre.IsLinearHom T.t.act act e.hom ∧ LamEq P.L e.hom e.hom T.t.PP.L (𝟙 T.t.G) (𝟙 T.t.G) := by
  intro laws E _ _ _ H R _ _ P act hadj
  have : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨L', hL', ⟨rig, hrig⟩, hsym, hamp, hk, hlam, prim⟩ :=
    exists_normalised_polarisation laws R P (act.act H.w0) (act.act (H.bar H.w0)) (act.hom _) (act.hom _)
      (by rw [← act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, act.one]) (hadj H.w0)
  let PP : RigLB P.A := ⟨L', rig, hL', hrig⟩
  let P' : Out.PolAV (Sp R) :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := L', isLB := hL', rigid := ⟨rig, hrig⟩,
      sym := hsym, ample := hamp, ktriv := hk }
  obtain ⟨cub⟩ := (laws.cube _ P' PP rfl).1
  have sym : PP.IsSymmetric :=
    GlobalTheory.PrimNorm.isSymmetric_of_hasGen PP (exists_gen_neg_of_sym laws.globalFns P.isAb hL' hsym)
  have lb : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ P.A)) {L : LB P.A.left}, L.IsLB → (cubeLB P.A x L).IsLB :=
    fun x L hL => DVR.linComb_isLB _ hL _ _
  have pts := ((GlobalTheory.LamCalc.lamEq_calculus _ P.A P.A P.A P.A P.A L' P.L P.L hL' P.isLB P.isLB
    (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)).2.1 hlam).2.2.2.2
  simp only [Category.comp_id] at pts
  have adj : ∀ a, LBIso (cubeLB P.A ![fst P.A P.A ≫ act.act a, snd P.A P.A] L')
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ act.act (H.bar a)] L') := fun a =>
    LBIso.trans (lb _ hL') (lb _ P.isLB) (lb _ hL') (pts _ _ _)
      (LBIso.trans (lb _ P.isLB) (lb _ P.isLB) (lb _ hL')
        (by simpa only [LamEq, Category.comp_id] using hadj a) (pts _ _ _).symm)
  exact ⟨{ t := { G := P.A, semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ P.isAb, act := act, PP := PP, cub := cub,
                  sym := sym, adj := adj, prim := prim },
           ab := P.isAb, g := P.g, dim := P.smoothDim, sym := hsym, ample := hamp, ktriv := hk },
    Iso.refl _, rfl, Serre.IsLinearHom.id act, LBIso.symm hlam⟩

end GlobalTheory.LamF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.LatticeData

theorem cc_eq_conj (D : D7) (x : D.host.E) : ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x :=
  bridge_star_holds D.R D.host x

theorem flagDomainConj_hostXi_eq_neg (D : D7) : ReciprocityTheory.ChartRestriction.G.FD.cc D.host.xi0 = -D.host.xi0 :=
  conj_xi0_alt D

theorem halfDifferent_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  exact (bB_ne D).1 (by rw [h]; simp)

theorem absNorm_halfDifferent_le (D : D7) :
    (Ideal.absNorm D.host.𝔟 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
  have ht : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
      (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)
  have hdvd : D.host.𝔟 ∣ differentIdeal ℤ (𝓞 D.host.E) := by
    rw [ht, D.host.𝔟_spec.1, mul_assoc]
    exact dvd_mul_right _ _
  have h1 := map_dvd Ideal.absNorm hdvd
  rw [NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 (NumberField.discr_ne_zero D.host.E)) h1
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast h2

theorem absNorm_mul_mem_one (D : D7) {a : D.host.E} (ha : a ∈ D.host.AA) :
    ∃ z : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E z = (Ideal.absNorm D.host.𝔟 : D.host.E) * a := by
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at ha
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero (bB_ne D).1] at ha
  obtain ⟨w, -, hw⟩ := (FractionalIdeal.mem_coeIdeal _).1
    (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem D.host.𝔟, rfl⟩))
  exact ⟨w, by rw [hw, map_natCast, mul_comm]⟩

theorem absNorm_ccK_mem (D : D7) : (Ideal.absNorm D.host.ccK : D.host.E) ∈ D.host.AA := by
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero (bB_ne D).1]
  intro y hy
  obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have h : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    rwa [map_natCast] at this
  exact (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mul_mem_right z _ h, by rw [map_mul, map_natCast]⟩

theorem exists_dataX_of_hasPrinc : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ σ, GoodEmb T.Q.c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M → ∀ k : (T.U j σ).Comp, ∃ Xx : ReciprocityTheory.ChartRestriction.G.FD.DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ Xx.k0 = 2 * xiR D ∧ (Xx.NA : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| ∧ Xx.NC ≤ Ideal.absNorm D.host.ccK := by
  intro D T h j hj σ hσ hP k
  obtain ⟨-, -, -, hx0, hx1, -⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have habs := h.xiAbs j hj σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ)) k
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
    (flagDomainConj_hostXi_eq_neg D) ((T.U j σ).X k).ξ0_im (habs _).symm
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((T.U j σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  have hM : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  obtain ⟨Xx, h1, h2, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((T.U j σ).X k) D.host.AA D.host.AAbar
    (xiR D) T.Q.l.M
    (fun a => by
      rw [cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (hP k)
  refine ⟨{ Xx with
    k0 := 2 * xiR D
    minWeight_pos := by positivity
    k0_le := by linarith
    ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((T.U j σ).X k).ξ0 from congrArg _ h1, habs]; ring
    NA := Ideal.absNorm D.host.𝔟
    NC := Ideal.absNorm D.host.ccK
    NA_pos := Nat.pos_of_ne_zero fun e => halfDifferent_ne_bot D (Ideal.absNorm_eq_zero_iff.1 e)
    NC_pos := Nat.pos_of_ne_zero fun e => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    NA_sub := fun x hx => ?_
    NC_sub := fun x hx => ?_ }, h1, h2, h3, rfl, absNorm_halfDifferent_le D, le_rfl⟩
  · rw [h3] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hv
      obtain ⟨z, hz⟩ := absNorm_mul_mem_one D ha
      rw [smul_smul, ← hz, algebraMap_smul]
      exact Xx.L'.smul_mem z hu
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact Xx.L'.smul_mem c hv
  · rw [h3]
    exact Submodule.subset_span ⟨_, absNorm_ccK_mem D, x, hx, rfl⟩

end GlobalTheory.LatticeData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorProductHomOfCmCurveHomFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

theorem IsKForm.map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D₁ D : Datum H} {ε : ℤˣ}
    {h₁ : D₁.La → D₁.La → OK H} {h : D.La → D.La → OK H} (k₁ : IsKForm D₁ ε h₁) (k : IsKForm D ε h)
    {L : Submodule (𝓞 E) D.La} (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E) (hf : ∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b)
    (a b : D₁.La) : h (f a) (f b) = h₁ (c • a) b := by
  apply Subtype.ext
  have e : H.w0 • ((f a : L) : D.La) = ((f (H.w0 • a) : L) : D.La) := by rw [map_smul]; rfl
  rw [k, k₁, e, hf, hf, smul_comm c H.w0 a]

theorem exists_famLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D₁ D : Datum H) (ε : ℤˣ) (h₁ : D₁.La → D₁.La → OK H) (h : D.La → D.La → OK H) (T₁ T : PAT H (Sp R)) (t : IsTen C D₁ h₁ T₁) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E), IsKForm D₁ ε h₁ → IsKForm D ε h → (∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b) → IsFam C T h L ψ →
  ∃ Φ : T₁.t.G ⟶ T.t.G, Serre.IsLinearHom T₁.t.act T.t.act Φ ∧ (∀ a, t.ten.tmul a ≫ Φ = ψ (f a)) ∧ LamEq T.t.PP.L Φ Φ T₁.t.PP.L (T₁.t.act.act c) (𝟙 T₁.t.G) := by
  intro E _ _ _ H R _ ω C D₁ D ε h₁ h T₁ T t L ψ f c k₁ k hf ⟨l, hadd, hsmul, hlam⟩
  let F : D₁.La →ₗ[OK H] Serre.Pts (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) C.P.A :=
    { toFun := fun a => Serre.Pts.mk _ (ψ (f a))
      map_add' := fun a b => Serre.Pts.ext (by rw [map_add (f := _)]; exact hadd _ _)
      map_smul' := fun s a => Serre.Pts.ext (by
        have e : f (s • a) = (s : 𝓞 E) • f a := f.map_smul (s : 𝓞 E) a
        rw [e]; exact hsmul _ _) }
  have hF : ∀ a, Serre.IsLinearHom C.act (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (F a).hom :=
    fun a => l (f a)
  have hm : IsMonHom (t.ten.lift F hF) := (t.ten.isLinearHom_lift F hF).isMonHom
  have ht : ∀ a, t.ten.tmul a ≫ t.ten.lift F hF = ψ (f a) := fun a => t.ten.tmul_lift F hF a
  refine ⟨t.ten.lift F hF, ⟨hm, fun s => ?_⟩, ht, ?_⟩
  · have := T₁.t.act.hom s
    have := T.t.act.hom s
    refine t.ten.hom_ext fun a => ?_
    rw [← Category.assoc, ← t.lin, ht, ← Category.assoc, ht, map_smul, hsmul]
  · refine _root_.GlobalTheory.LamCalc.lamEq_of_tmul _ _ _ _ _ _ _ t.ten _ _ _ t.ten _ _ _ _ _ _ _ _ T.t.PP.isLB T₁.t.PP.isLB
      ⟨T.t.cub.t, T.t.cub.isGen⟩ ⟨T₁.t.cub.t, T₁.t.cub.isGen⟩ hm hm (T₁.t.act.hom c) inferInstance fun a b => ?_
    rw [ht, ht, ← t.lin, Category.comp_id]
    have e := hlam (f a) (f b)
    rw [k₁.map_eq k f c hf] at e
    exact LBIso.trans (LamCalc.cubeLB_isLB T.t.PP.isLB _) (LamCalc.cubeLB_isLB C.P.isLB _)
      (LamCalc.cubeLB_isLB T₁.t.PP.isLB _) e (LBIso.symm (t.lam (c • a) b))

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.TripleModel

section Tensor

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X Y : Over S} {X' Y' : Over S'}

theorem isPullback_tensor {a : X'.left ⟶ X.left} {b : Y'.left ⟶ Y.left} (ha : IsPullback a X'.hom X.hom f)
    (hb : IsPullback b Y'.hom Y.hom f) {c : (X' ⊗ Y').left ⟶ (X ⊗ Y).left}
    (h₁ : c ≫ (fst X Y).left = (fst X' Y').left ≫ a) (h₂ : c ≫ (snd X Y).left = (snd X' Y').left ≫ b) :
    IsPullback c (X' ⊗ Y').hom (X ⊗ Y).hom f := by
  have h : IsPullback (fst X' Y').left (snd X' Y').left X'.hom Y'.hom := .of_hasPullback _ _
  have h₀ : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := .of_hasPullback _ _
  have h₃ : IsPullback c (snd X' Y').left (snd X Y).left b := by
    refine IsPullback.of_right ?_ h₂ h₀
    rw [h₁, hb.w]
    exact h.paste_horiz ha
  rw [← Over.w (snd X' Y'), ← Over.w (snd X Y)]
  exact h₃.paste_vert hb

end Tensor

section Cube

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] {φ : G'.left ⟶ G.left} {M : LB G.left} {M' : LB G'.left}

theorem lbIso_cube_pull (h : IsGrpPullback G' G f φ) (hM : M.IsLB) (hM' : M'.IsLB) (e : LBIso (M.pull φ) M')
    {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    LBIso ((cubeLB G x M).pull U.left) (cubeLB G' x' M') := by
  have hc : (cubeLB G x M).IsLB := DVR.linComb_isLB _ hM _ _
  have h₁ : LBIso ((cubeLB G x M).pull U.left) (cubeLB G' x' (M.pull φ)) :=
    LBIso.chartPull (Geo.Tor.chartPullPull _ _ U.left rfl)
      (chartPullLinComb M _ _ _ _ U.left fun I => psum_push h _ _ U hx I.down) (PolBaseChange.lbIso_refl hc)
  exact LBIso.trans (pull_isLB hc _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (DVR.linComb_isLB _ hM' _ _) h₁
    (PowPrimitive.lbIso_linComb e _ _)

theorem lbIso_cube_of_eq (hM : M.IsLB) {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x y : Fin n → (T ⟶ G))
    (h : ∀ i, ρ ≫ x i = ρ ≫ y i) : LBIso ((cubeLB G x M).pull ρ.left) ((cubeLB G y M).pull ρ.left) :=
  LBIso.chartPull (chartPullOut M _ _ ρ.left _ fun I => PrimNorm.psum_pre ρ x (fun i => ρ ≫ x i) (fun _ => rfl) I.down)
    (chartPullOut M _ _ ρ.left _ fun I => PrimNorm.psum_pre ρ y (fun i => ρ ≫ x i) h I.down)
    (PolBaseChange.lbIso_refl (L := cubeLB G (fun i => ρ ≫ x i) M) (DVR.linComb_isLB _ hM _ _))

theorem exists_gen_theta_zero (hM : M.IsLB) :
    ∃ t : LB.Gen ((Theta G M).pull (eSec (G ⊗ G ⊗ G))), t.IsGen := by
  have e : η[G ⊗ G ⊗ G] = lift (1 : 𝟙_ _ ⟶ G) (lift (1 : 𝟙_ _ ⟶ G) (1 : 𝟙_ _ ⟶ G)) := by
    ext <;> simp [Hom.one_def]
  obtain ⟨t, ht⟩ := (PrimNorm.hasGen_iff hM
    (fun I : thK => (lift (1 : 𝟙_ _ ⟶ G) (lift (1 : 𝟙_ _ ⟶ G) (1 : 𝟙_ _ ⟶ G))).left ≫ thφ G (x3 G) I) thε).2
    ((prod_cub _ _ _ (PrimNorm.cls M)).trans (by simp))
  exact gen_chartPull (chartPullOut M (thφ G (x3 G)) thε (eSec (G ⊗ G ⊗ G)) _ fun I => by rw [eSec, e]) t ht

end Cube

theorem exists_gen_of_lbIso {X : Scheme.{0}} {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) (H : LBIso L N)
    (h : ∃ t : L.Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen :=
  (CechPic.iso_triv_iff N).1 (LBIso.trans (LB.isLB_triv X) hL hN ((CechPic.iso_triv_iff L).2 h) H)

theorem exists_triple_of_abelian_model : Out.Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (t₀ : SAB H (Sp K)) (B : Over (Sp R)) [GrpObj B] (φ : t₀.G.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback t₀.G B (spMap (algebraMap R K)) φ → ∃ (t : SAB H (Sp R)) (m : SABMap t₀ t (spMap (algebraMap R K))) (e : t.G ≅ B), IsMonHom e.hom ∧ m.φ ≫ e.hom.left = φ := by
  intro hL hext E _ _ _ H R K _ _ _ _ _ t₀ B _ φ hB h
  have := hB.comm
  have hB₂ := AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB
  have hB₃ := AbelianSchemeGerms.isAbelianScheme_tensor B _ hB hB₂
  obtain ⟨act, hact⟩ := exists_oAct_extend_dedekind hext R K (𝓞 E) B t₀.G φ hB h t₀.act
  obtain ⟨M, hM⟩ := exists_rigLB_extension_dedekind R K B hB _ φ t₀.G.hom h.1 t₀.PP.L t₀.PP.isLB
  have lb : ∀ {T : Over (Sp R)} {n : ℕ} (x : Fin n → (T ⟶ B)) {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB :=
    fun x L hL => DVR.linComb_isLB _ hL _ _
  have lb₀ : ∀ {T : Over (Sp K)} {n : ℕ} (x : Fin n → (T ⟶ t₀.G)), (cubeLB t₀.G x t₀.PP.L).IsLB :=
    fun x => DVR.linComb_isLB _ t₀.PP.isLB _ _
  have pa : ∀ {T : Over (Sp K)} (x : T ⟶ t₀.G) a,
      pushPt h.1.w (x ≫ t₀.act.act a) = pushPt h.1.w x ≫ act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  let U₂ := lift (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))
  have p₂ : IsPullback U₂.left (t₀.G ⊗ t₀.G).hom (B ⊗ B).hom (spMap (algebraMap R K)) :=
    isPullback_tensor h.1 h.1
      (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))))
      (congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))))
  let U₃ := lift (pushPt h.1.w (x3 t₀.G 0)) (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))
  have p₃ : IsPullback U₃.left (t₀.G ⊗ t₀.G ⊗ t₀.G).hom (B ⊗ B ⊗ B).hom (spMap (algebraMap R K)) := by
    refine isPullback_tensor h.1 p₂ (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (x3 t₀.G 0))
        (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))))
      ((congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (x3 t₀.G 0))
        (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2))))).trans ?_)
    apply pullback.hom_ext
    · refine (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (lift_fst
        (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G)))).symm)
    · refine (congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (lift_snd
        (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G)))).symm)
  have hT : ∃ t : LB.Gen (Theta B M.L), t.IsGen :=
    TrivDedekind.exists_gen_of_generic R K (B ⊗ B ⊗ B) hB₃ _ U₃.left _ p₃ (Theta B M.L) (lb _ M.isLB) (exists_gen_theta_zero M.isLB)
      (exists_gen_of_lbIso (lb₀ _) (pull_isLB (lb _ M.isLB) _)
        (lbIso_cube_pull h M.isLB t₀.PP.isLB hM (x3 t₀.G) (x3 B) U₃
          (fun i => by fin_cases i <;> simp [U₃, x3])).symm ⟨t₀.cub.t, t₀.cub.isGen⟩)
  have ha : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M.L)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M.L) := by
    intro a
    have := act.hom a
    have := act.hom (H.bar a)
    refine IsoDescent.lbIso_of_field R K (algebraMap R K) (IsFractionRing.injective R K) (B ⊗ B) hB₂ _ U₂.left _ p₂ _ _
      (lb _ M.isLB) (lb _ M.isLB) (lbIso_cube_of_eq M.isLB η[B ⊗ B] _ _ fun i => ?_) ?_
    · fin_cases i <;> simp
    · refine LBIso.trans (pull_isLB (lb _ M.isLB) _) (lb₀ _) (pull_isLB (lb _ M.isLB) _)
        (lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U₂ fun i => ?_)
        (LBIso.trans (lb₀ _) (lb₀ _) (pull_isLB (lb _ M.isLB) _) (t₀.adj a)
          (lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U₂ fun i => ?_).symm)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U₂])
        · simp [U₂]
      · fin_cases i
        · simp [U₂]
        · exact (pa _ _).trans (by simp [U₂])
  obtain ⟨PP, cub, sym, hPP, -, prim, adj⟩ :=
    PrimNorm.exists_primitive_normalisation hL.globalFns E H _ B act M.L hB M.isLB hT ha
  let t : SAB H (Sp R) := ⟨B, isSemiAbelian_of_isAbelianScheme B hB, act, PP, cub, sym, adj, prim⟩
  have hφ : LBIso t₀.PP.L (PP.L.pull φ) := by
    let U := pushPt h.1.w (𝟙 t₀.G)
    have eU : U.left = φ := Category.id_comp _
    have h₁ : LBIso ((cubeLB B ![𝟙 B, act.act H.w0] M.L).pull U.left)
        (cubeLB t₀.G ![𝟙 t₀.G, t₀.act.act H.w0] t₀.PP.L) := by
      refine lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U fun i => ?_
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    rw [eU] at h₁
    exact LBIso.trans t₀.PP.isLB (lb₀ _) (pull_isLB PP.isLB _) t₀.prim
      (LBIso.trans (lb₀ _) (pull_isLB (lb _ M.isLB) _) (pull_isLB PP.isLB _) h₁.symm
        (PowPrimitive.lbIso_linComb hPP.symm _ _))
  obtain ⟨m, hm⟩ := CartTriple.exists_tripleMap hL.globalFns E H _ _ _ t₀ t φ (PolPull.isAbelianScheme_of_isGrpPullback hB h) h hact hφ
  exact ⟨t, m, Iso.refl B, inferInstanceAs (IsMonHom (𝟙 B)), (Category.comp_id _).trans hm⟩

end GlobalTheory.CM.TripleModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormEqPiMulHermForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.CM.LieMetric

theorem form_eq_sum_sum {K : Type} [Field K] {g : ℕ} (h : HermFam K (Fin g → K)) (s : K →+* ℂ) (x y : Fin g → K) :
    h.form s x y = ∑ j, ∑ i, s (y j) * star (s (x i)) * h.form s (Pi.single i 1) (Pi.single j 1) := by
  rw [form_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h.conj_symm, form_sum_right, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.conj_symm, _root_.mul_assoc]
  rfl

theorem hermForm_sum_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin n → ℂ) (X : Fin n → Fin g → ℂ) :
    hermForm Hm (∑ j, a j • X j) (∑ i, b i • X i) = ∑ j, ∑ i, a j * star (b i) * hermForm Hm (X j) (X i) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_eq_pi_mul_hermForm : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (s : K →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ), IsPolFibre s F.P₀ Q ψ → u.IsAH Hm χ → ∀ (c c' : Fin F.P₀.g → K) (w w' : epsR K ⟶ F.P₀.A) (v v' : epsR ℂ ⟶ Q.A) (W W' : Fin Q.g → ℂ), IsLieComb c F.v w → IsLieComb c' F.v w' → IsVecOver s ψ w v → IsVecOver s ψ w' v' → u.IsDiff W v → u.IsDiff W' v' → h.form s c c' = Real.pi * hermForm Hm W' W := by
  intro hU _ K _ _ P F h H s Q ψ u Hm χ hQ hA c c' w w' v v' W W' hw hw' hv hv' hW hW'
  obtain ⟨Q₀, ψ₀, v₀, u₀, Hm₀, χ₀, W₀, a₀, b₀, c₀, d₀⟩ := H s
  obtain ⟨-, -, -, -, t1, -, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q _ u Hm χ hA
  choose x hx using fun i => (existsUnique_isVecOver hQ.2.1.1 (F.v i)).exists
  have hxt : ∀ i, IsTangent (x i) := fun i => (hx i).isTangent hQ.2.1 (F.basis.1 i)
  choose X hX using fun i => (t1 _ (hxt i)).exists
  have key : ∀ (c : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A) (v : epsR ℂ ⟶ Q.A) (W : Fin Q.g → ℂ), IsLieComb c F.v w →
      IsVecOver s ψ w v → u.IsDiff W v → W = ∑ i, s (c i) • X i := fun c w v W hw hv hW => by
    have h1 := (lieComb_baseChange K ℂ s _ _ ψ hQ.2.1 _ F.v w c x v hx hw).1 hv
    have h3 : IsTangent v := by
      rw [(Chart.isLieComb_iff _ x v).1 h1, ← Chart.isTan_iff]
      refine List.prod_induction Chart.IsTan (fun a b ha hb => Chart.isTan_mul ha hb) Chart.isTan_one ?_
      intro a ha
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
      exact Chart.isTan_scale (s (c i)) ((Chart.isTan_iff _).2 (hxt i))
    exact (t1 v h3).unique hW (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u X x _ v hxt hX h1)
  rw [key c w v W hw hv hW, key c' w' v' W' hw' hv' hW', hermForm_sum_sum, form_eq_sum_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [d₀, hermForm_eq hU a₀ hQ b₀ hA F.basis.1 c₀ (fun i => ⟨hx i, hX i⟩)]
  ring

end GlobalTheory.CM.LieMetric
end
end

