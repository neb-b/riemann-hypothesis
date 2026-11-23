module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieLineDegreeOfEigenLineDegreeFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem lamDegSt_of_degSt : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → LamDegSt H (logOm E χ).re := by
  intro hD hU hL E _ _ _ H _ χ hχ _ l c hstar nΨ n' f o La ho
  obtain ⟨-, -, -, -, hΨ, h', -, -, -, tΨ, t', -, -, -, -, -, vΨ, v', -⟩ := ho
  obtain ⟨hb, -, -, ρ, hρ, h1, h2, -⟩ := labK_spec E H l c o.K₁
  exact ⟨fun k => _root_.GlobalTheory.LamF.ndeg_vecLine_eq hD hU hL E H χ hχ hstar o.K₁ o.AΨ o.oaΨ o.xΨ o.φΨg (psiSet H) o.τΨ (labK c o.K₁) ρ
      hΨ hb.1 hρ h1 tΨ k _ (vΨ k),
    fun k => _root_.GlobalTheory.LamF.ndeg_vecLine_eq hD hU hL E H χ hχ hstar o.K₁ o.A' o.oa' o.x' o.φ'g (psiSet H)ᶜ o.τ' (labK c o.K₁) (-ρ)
      h' hb.1 (by rw [neg_sq, hρ]) h2 t' k _ (v' k)⟩

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.EllExists

theorem isQuadLattice_of_linear {g g' : ℕ} (hg : g = 1) (hg' : g' = 1) {Λ : Submodule ℤ (Fin g → ℂ)}
    {Λ' : Submodule ℤ (Fin g' → ℂ)} (hd : DiscreteTopology Λ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (hF : ∀ z, z ∈ Λ ↔ F z ∈ Λ') {d : ℕ} {c : ℂ} (hc : c ≠ 0) (h : PureType.IsQuadLattice Λ' d c) :
    ∃ c' : ℂ, c' ≠ 0 ∧ PureType.IsQuadLattice Λ d c' := by
  subst hg hg'
  obtain ⟨a, ha⟩ : ∃ a : ℂ, ∀ z, F z = fun _ => a * z 0 := ⟨F (fun _ => 1) 0, fun z => by
    have e : z = z 0 • fun _ => (1 : ℂ) := by
      funext i
      fin_cases i
      simp
    funext i
    fin_cases i
    conv_lhs => rw [e, map_smul]
    simp [mul_comm]⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    have ht : (Λ : Set (Fin 1 → ℂ)) = Set.univ := Set.eq_univ_of_forall fun z => (hF z).2 (by
      rw [ha]
      simp only [zero_mul]
      exact Λ'.zero_mem)
    have h1 : IsDiscrete (Λ : Set (Fin 1 → ℂ)) := ⟨hd⟩
    rw [ht, isDiscrete_univ_iff] at h1
    have := (isClopen_discrete ({0} : Set (Fin 1 → ℂ))).eq_univ ⟨0, rfl⟩
    have h2 : (1 : Fin 1 → ℂ) ∈ ({0} : Set (Fin 1 → ℂ)) := this ▸ Set.mem_univ _
    exact one_ne_zero h2
  refine ⟨c / a, div_ne_zero hc ha0, fun z => ?_⟩
  rw [hF, h, ha]
  refine exists₂_congr fun m n => ⟨fun e => ?_, fun e => ?_⟩
  · funext i
    fin_cases i
    have := congrFun e 0
    field_simp
    field_simp at this
    simpa [mul_comm a] using this
  · funext i
    rw [e]
    field_simp

theorem isQuadLattice_of_isGrpPullback (hU : ThetaUnifAV) (hL : Out.Laws) {R : Type} [CommRing R]
    (P : Out.PolAV (Sp R)) (hg : P.g = 1) (σ : R →+* ℂ) {d : ℕ}
    (h : ∀ (Q : Out.PolAV (Sp ℂ)) (φ : Q.A.left ⟶ P.A.left), IsPolFibre σ P Q φ → ∀ u : HolUnif Q.A Q.L Q.g,
      ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ d c)
    (Q : Out.PolAV (Sp ℂ)) (hQ : Q.g = 1) (φ : Q.A.left ⟶ P.A.left) (hφ : IsGrpPullback Q.A P.A (spMap σ) φ)
    (u : HolUnif Q.A Q.L Q.g) : ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ d c := by
  obtain ⟨Q₀, φ₀, h₀⟩ := exists_isPolFibre hL.polBaseChange σ P
  obtain ⟨rig, hrig⟩ := Q₀.rigid
  obtain ⟨u₀, -, -, -, -, -, t₁, t₂, -⟩ := hU Q₀ rig hrig
  obtain ⟨c, hc, hΛ⟩ := h Q₀ φ₀ h₀ u₀
  obtain ⟨f, hf, ef⟩ := NormHom.exists_monHom_lift hφ h₀.2.1 (𝟙 P.A)
  obtain ⟨F, hF, hF', -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q₀.A Q.isAb Q₀.isAb Q.L Q₀.L Q.g Q₀.g u u₀ t₁ t₂ f hf
  refine isQuadLattice_of_linear hQ (h₀.1.trans hg) u.discrete F (fun z => ⟨hF' z, fun hz => ?_⟩) hc hΛ
  rw [← u₀.ker, hF] at hz
  rw [← u.ker]
  apply NormHom.push_inj hφ
  have e := NormHom.push_comp hφ h₀.2.1 ef (u.ex z)
  rw [hz, map_one, Category.comp_id] at e
  rw [map_one, e]

theorem exists_ell_pos (hC : CMCurve) (hU : ThetaUnifAV) (hL : Out.Laws) (hX : HomExtDvr) {E : Type} [Field E]
    [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (hχ : IsKroneckerChar χ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ),
      ((ω : M) : ℂ) = (1 + Complex.I * √H.d) / 2 ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧
      C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  have hm := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) (by omega)
  obtain ⟨M, _, w, P, v, hw, hg, hv, ⟨P₀, φ, v₀, W, hφ, hv₀, hb₀, hW, hWW, hWv⟩, hΛ, n, hn0, hn, hx, -⟩ :=
    chowla_selberg_lie_lines hC (by omega) H.d_prime.squarefree (by omega) h2 hr hχ
  have := P₀.isAb.comm
  have := P.isAb.comm
  obtain ⟨a₀, ha₀, -⟩ := _root_.GlobalTheory.CM.exists_okAct_of_equation E H _ P₀.A W hW hWW
  obtain ⟨a, ha⟩ := exists_oAct_extend_dedekind hX (𝓞 M) M (OK H) P.A P₀.A φ P.isAb hφ.2.1 a₀
  have hvt : IsTangent v := hv.1 0
  have := a.hom (wK H)
  obtain ⟨c, hc, -⟩ := hv.2 _ (HomLinear.isTangent_comp (a.act (wK H)) hvt)
  obtain ⟨ω, rfl⟩ : ∃ ω, c = ![ω] := ⟨c 0, by funext i; fin_cases i; rfl⟩
  have hc₀ := (lieComb_baseChange _ _ (algebraMap (𝓞 M) M) P.A P₀.A φ hφ.2.1 1 ![v] _ ![ω] ![v₀] (v₀ ≫ W)
    (fun j => by fin_cases j; exact hv₀) hc).1 (NormHom.isVecOver_comp hv₀ (ha₀ ▸ ha (wK H)))
  have hω : (ω : M) = w := congrFun ((hb₀.2 _ (HomLinear.isTangent_comp W (hb₀.1 0))).unique hc₀ hWv) 0
  have hσ : Function.Injective ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) :=
    (algebraMap M ℂ).injective.comp (IsFractionRing.injective (𝓞 M) M)
  obtain ⟨L', h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := _root_.GlobalTheory.CM.exists_normalised_polarisation hL (𝓞 M) P (a.act (wK H)) (a.act (EllConj.barK H (wK H)))
    (a.hom _) (a.hom _) (by rw [← a.add, add_comm, EllConj.barK_wK_add, a.one])
    (_root_.GlobalTheory.CurveAdjoint.lamEq_act_bar hU hL E H (𝓞 M) _ P a hσ hg _ _ rfl)
  let P' : Out.PolAV (Sp (𝓞 M)) := ⟨P.A, P.isAb, P.g, P.smoothDim, L', h₁, h₂, h₃, h₄, h₅⟩
  have key : ∀ (s : M →+* ℂ) r, IsLieNormSq P' v (s.comp (algebraMap (𝓞 M) M)) r → r = n s := fun s r h => by
    have h1 : IsLieComb ![(1 : 𝓞 M)] ![v] (v ≫ 𝟙 P.A) := by
      rw [LieComb.isLieComb_iff_tanExp, Category.comp_id]
      have e : (![1] : Fin 1 → 𝓞 M) = Pi.single 0 1 := by
        funext i
        fin_cases i
        simp
      rw [e]
      exact (LieComb.tanExp_single hv.1 0).symm
    have e := NormHom.lieNormSq_comp hU hL (𝓞 M) P P' (𝟙 P.A) (𝟙 P.A) v 1 _ (n s) r inferInstance inferInstance h₆ hvt
      h1 ((hn s _).2 rfl) (by rwa [Category.comp_id])
    simpa using e
  refine ⟨M, inferInstance, ω, ⟨P', hg, a, v, hv, hc, _root_.GlobalTheory.CurveAdjoint.lamEq_act_bar hU hL E H (𝓞 M) _ P' a hσ hg, h₇⟩, -meanLog M n,
    hω ▸ hw, fun Q ψ hψ u => ?_, ⟨n, fun s => ⟨hn0 s, fun r => ⟨key s r, fun e => ?_⟩⟩, rfl⟩, hx⟩
  · refine isQuadLattice_of_isGrpPullback hU hL P hg _ (fun Q ψ hψ u => ?_) Q (hψ.1.trans hg) ψ hψ.2.1 u
    obtain ⟨c, hc, h⟩ := hΛ Q ψ hψ u
    rw [hw] at h
    exact ⟨c, hc, h⟩
  · obtain ⟨r', hr'⟩ := exists_isLieNormSq hU hL.polBaseChange P' hvt (s.comp (algebraMap (𝓞 M) M))
    rwa [e, ← key s r' hr']

theorem exists_ell : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) → ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ), 2 * ((ω : M) : ℂ) - 1 = ρ ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧ C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  intro hC hU hL hX E _ _ _ H _ χ hχ ρ hρ
  obtain ⟨M, _, ω, C, x, hω, hp, hx, hv⟩ := exists_ell_pos hC hU hL hX H hχ
  have e : ρ ^ 2 = (Complex.I * √H.d) ^ 2 := by
    rw [hρ, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with rfl | rfl
  · exact ⟨M, inferInstance, ω, C, x, by rw [hω]; ring, hp, hx, hv⟩
  · obtain ⟨a, -, h₁, h₂, h₃⟩ := EllConj.exists_conj_action E H (𝓞 M) ω C
    refine ⟨M, inferInstance, 1 - ω, ⟨C.P, C.dim, a, C.v, C.basis, h₁, h₂, h₃⟩, x, ?_, hp, hx, hv⟩
    have : (((1 - ω : 𝓞 M) : M) : ℂ) = 1 - ((ω : M) : ℂ) := by simp
    rw [this, hω]
    ring

end GlobalTheory.CM.EllExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRosatiActionWeilPairingBalancedTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_oAct_rosatiConj : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E), (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))), ∃ oa : T.pol.OAct (𝓞 E), oa.act = T.t.act.act ∧ RosatiConj T.pol oa := by
  intro hL E _ _ _ _ H hs K _ _ T
  have : IsCommMonObj T.pol.A := T.pol.isAb.comm
  obtain ⟨ra, hra⟩ := (ringAct_iff_oAct (𝓞 E) (Sp (𝓞 K)) T.pol.A).2 T.t.act
  have hlam : ∀ a : 𝓞 E, LamEq T.pol.L (ra.act a) (𝟙 T.pol.A) T.pol.L (𝟙 T.pol.A) (ra.act (star a)) := by
    intro a
    rw [hra, hs]
    have h := T.t.adj a
    simpa [LamEq] using h
  refine ⟨⟨ra, fun a => (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hL.globalFns _ T.pol _ _ (ra.hom a) (ra.hom _)).2 (hlam a)⟩,
    hra, ?_⟩
  intro a Tb k x z c hk hx hz
  have hp : ∀ (n : ℕ) (p : Tb ⟶ T.pol.A), pnsmulPt n p = p ^ n := by
    intro n p
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  have hu : toUnit Tb ≫ η[T.pol.A] = (1 : Tb ⟶ T.pol.A) := rfl
  rw [hp, hu] at hx hz
  have := _root_.GlobalTheory.PairingScheme.weilIs_iff_of_lamEq hL (𝓞 K) T.pol T.pol T.pol T.pol (ra.act a) (𝟙 _) (𝟙 _) (ra.act (star a)) (ra.hom a)
    inferInstance inferInstance (ra.hom _) (hlam a) Tb k x z c hk hx hz
  simpa using this

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormLetterLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem form_letter_le (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E]
    [StarRing (𝓞 E)] {K : Type} [Field K] [NumberField K] {S : Set (E →+* ℂ)}
    (A B : Out.PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left)
    (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (hx : IsFibreOf A x (gmap K) φ)
    (hT : IsLieType A oa x φ τ lab) (F' : GenFib B) (h' : HermFam K (Fin F'.P₀.g → K)) (H' : F'.IsHerm h')
    (f : A.A ⟶ B.A) (hf : IsMonHom f) (a : 𝓞 E)
    (hW : ∀ (Tb : Over (Sp (𝓞 K))) (k : ℕ) (x y : Tb ⟶ A.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k →
      pnsmulPt k x = toUnit Tb ≫ η[A.A] → pnsmulPt k y = toUnit Tb ≫ η[A.A] →
      (Out.WeilIs B.A B.L k (x ≫ f) (y ≫ f) c ↔ Out.WeilIs A.A A.L k (x ≫ oa.act a) y c))
    (La : ℝ) (hb : ∀ τ : E →+* ℂ, ‖τ (a : E)‖ ≤ La ^ 2) (i : Fin x.P.g) (ℓ : MLine K) (hℓ : IsVecLine A x φ i ℓ)
    (U : Fin F'.P₀.g → K) (w' : epsR K ⟶ F'.P₀.A) (hw : IsLieComb U F'.v w')
    (e : w'.left ≫ F'.φ = (x.v i).left ≫ φ ≫ f.left) (s : K →+* ℂ) :
    (h'.form s U U).re ≤ (La * ℓ.n s) ^ 2 := by
  have hp : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).1 hx
  obtain ⟨h, H⟩ := (GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL K A (GenFib.mk x.P φ hp x.v x.basis)).1
  have hg : IsMonHom (oa.act a) := oa.hom a
  obtain ⟨w, hw1, hw2⟩ := hT a i
  have h1 := _root_.GlobalTheory.LamF.LenOne.form_image_le hU hL K A B (GenFib.mk x.P φ hp x.v x.basis) F' h h' f (oa.act a) H H' hf hg
    (lamEq_of_weilIs_all_points hL K A B f (oa.act a) hf hg hW) i _ w U w' hw1 hw2 hw e s
  have h2 := GlobalTheory.CM.LieMetric.vecLine_norm_sq_eq_form hU hL K A x φ hp h H i ℓ hℓ s
  refine h1.trans ?_
  rw [mul_pow]
  refine le_trans (le_of_eq (congrArg _ h2.symm)) ?_
  exact mul_le_mul_of_nonneg_right (hb (s.comp (lab (τ i)))) (sq_nonneg _)

theorem lamLen : ThetaUnifAV → Out.Laws → LamLenSt := by
  intro hU hL E _ _ _ _ H l c _ nΨ n' f o La hG L hLg σ
  obtain ⟨-, -, -, hB, hΨ, hA', -, -, -, tΨ, t', -, -, hI, hP, hb, vΨ, v', -, hgood, -, harch, -⟩ := hG
  have hp : IsPolFibre (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB.P o.φB :=
    (isFibreOf_iff_isPolFibre (𝓞 o.K₁) o.K₁ (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB o.φB).1 hB
  obtain ⟨h, Hh⟩ := (GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL o.K₁ o.B
    (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis)).1
  obtain ⟨g1, g2⟩ := gram_stdBasis_posDef_and_hq o.K₁ o.xB.P.g h σ
  refine ⟨_, g1, ?_, fun k => ?_⟩
  · have := _root_.GlobalTheory.CM.TopLieVector.sq_eq_det_gram hU hL o.K₁ o.B o.xB o.φB hp h Hh o.Tl o.LamL σ (harch σ)
    exact ((congrArg Real.sqrt this).symm.trans (Real.sqrt_sq (hgood.2 σ).le)).symm
  · rw [g2]
    obtain ⟨w, hw1, hw2⟩ := hLg.2.2.1 k
    have h4 := hLg.2.2.2 k
    unfold LamLetters.IsLetter at hw1
    cases hs : L.src k with
    | inl q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.AΨ o.B o.oaΨ o.xΨ o.φΨg (S := psiSet H) o.τΨ _ hΨ tΨ
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φΨ q.1) (hI.1 _) (o.hΨ q.1) (hP.2.2.1 q.1) La
        (hb.1 q.1) q.2 _ (vΨ q.2) _ w hw2 hw1 σ
    | inr q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.A' o.B o.oa' o.x' o.φ'g (S := (psiSet H)ᶜ) o.τ' _ hA' t'
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φ' q.1) (hI.2.1 _) (o.h' q.1) (hP.2.2.2 q.1) La
        (hb.2 q.1) q.2 _ (v' q.2) _ w hw2 hw1 σ

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingIffOfCubeLBPairingIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem weilIs_iff_of_lamEq_id : Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A) (g : A.A ⟶ A.A), IsMonHom f → IsMonHom g → LamEq B.L f f A.L g (𝟙 A.A) → ∀ (Tb : Over (Sp (𝓞 K))) (k : ℕ) (x y : Tb ⟶ A.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k → pnsmulPt k x = toUnit Tb ≫ η[A.A] → pnsmulPt k y = toUnit Tb ≫ η[A.A] → (Out.WeilIs B.A B.L k (x ≫ f) (y ≫ f) c ↔ Out.WeilIs A.A A.L k (x ≫ g) y c) := by
  intro hL K _ _ A B f g hf hg hlam Tb k x y c hk hx hy
  have h1 : toUnit Tb ≫ η[A.A] = (1 : Tb ⟶ A.A) := rfl
  have hp (n : ℕ) (a : Tb ⟶ A.A) : pnsmulPt n a = a ^ n := by
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  rw [hp, h1] at hx hy
  have h := PairingScheme.weilIs_iff_of_lamEq hL (𝓞 K) A A B A f f g (𝟙 A.A) hf hf hg inferInstance hlam
    Tb k x y c hk hx hy
  rwa [Category.comp_id] at h

end GlobalTheory.LamF
end

