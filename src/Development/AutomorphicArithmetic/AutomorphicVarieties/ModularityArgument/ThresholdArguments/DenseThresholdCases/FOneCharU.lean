module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.OneCharU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigEnd3
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumberU3US
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyUnramifiedCoefficients
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle0001

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Z.J
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
private theorem oneChar_unramU (hC : U3.CohInp) (hLM : LemmaM) (hLM' : LemmaM') (hLP : LemmaP) (hK : _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW)
    (hRI : _root_.UpperTheory.V.Th.RigidityFirstCase) (hRII : _root_.UpperTheory.V.Th.RigiditySecondCase) (hAd : _root_.UpperTheory.V.Z.J.AdmI_s) (hA : _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt)
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (he : eO l c.O = 1) (hG : GD Ω K l e ψ) (ι : Qbar l ≃+* ℂ) (σ : G K Ω) (t : Qbar l)
    (ht : t = algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ) : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ))⁻¹ : c.Oˣ) : c.O)))
    (hne : ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ →
      (ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ t) :
    Vlen Ω c e ψ ≠ ⊤ ∧ ∃ X : Finset (G K Ω →* GL (Fin 3) (Qbar l)),
      (∀ ρ ∈ X, _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ) ∧ (∀ ρ ∈ X, ∀ ρ' ∈ X, Af.RepIso ρ ρ' → ρ = ρ') ∧
      Vn Ω c e ψ ≤ 2 * ∑ ρ ∈ X, vl l ((ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t) := by
  classical
  obtain ⟨D⟩ := exists_dat hG
  obtain ⟨g₁, hM, hFin, hB, hW⟩ := hA Ω K l c N e ψ D he ι
  obtain ⟨U⟩ := exists_uLoc hC D
  obtain ⟨S⟩ := exists_ring hC D U g₁ hM
  obtain ⟨M⟩ := exists_model hC hLP D hM S
  have hmult : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, HasMult D.η (push f S.r.hom) := fun f g => S.r.hasMult g
  let ρ : (S.R →ₐ[c.O] PadicAlgCl l) → (G K Ω →* GL (Fin 3) (Qbar l)) := fun f => D.rhoK (push f S.r.hom) (hmult f)
  have hσ : D.η (galEmb ℚ K Ω σ) = 1 := by
    rw [← MonoidHom.mem_ker, D.η_ker]
    exact galEmb_mem ℚ K Ω σ
  have htr : ∀ f, trDiff D.η D.Ψ S.r.hom (galEmb ℚ K Ω σ) f =
      (ρ f σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t := by
    intro f
    let g := galEmb ℚ K Ω σ
    have htrace : (r0 D.η D.Ψ g).mat.trace = (D.Ψ g : c.O) + 1 + ((D.Ψ g)⁻¹ : c.Oˣ).val := by
      simp [GG.mat, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three, wt1]
    rw [trDiff, htrace, ht]
    congr 1
    exact AddMonoidHom.map_trace (f : S.R →+* PadicAlgCl l) _
  have hadm : ∀ f, TwoPt (η := D.η) S.r.hom f → _root_.UpperTheory.V.Z.J.Adm3U_s ι e N (ρ f) ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) (ρ f) := by
    intro f hf
    have hp := isPt_push D hM S f hf.1
    have hpush : IsPush (f.comp (entAlg c.O S.r.hom).val) S.r.hom (push f S.r.hom) :=
      fun g => ⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩
    rcases (twoPt_shape S hG.l_odd hM f hf).1 with h | h
    · exact Or.inl (hAd D hM S f hf.1 (hmult f) ι h (hB U S _ _ _ hpush h))
    · exact Or.inr (_root_.UpperTheory.GalN.V.adm2B_rhoK_of_typeII_of_modular_extensions hC D hM hp ι h
        (hW U S _ _ hpush h (typeII_facts hC D hM hp h).1))
  obtain ⟨hlen, T, hT, hTo, hle⟩ := model_upper S M hG.l_odd hM hLM (hFin U S)
    (_root_.UpperTheory.V.Z.J.ptHyp_of_autB_of_lemW_of_isBase hC hK hRI hRII D hM S ι hB hW M.x₀ M.base) (galEmb ℚ K Ω σ) hσ
    fun f hf => by rw [htr]; exact sub_ne_zero.2 (hne _ (hadm f hf))
  have hV := vlen_le hC hLM' D hM S M
  have hinj : ∀ f ∈ T, ∀ f' ∈ T, Af.RepIso (ρ f) (ρ f') → f = f' := by
    rintro f hf f' hf' ⟨g, hg⟩
    obtain ⟨s, hs⟩ := (twoPt_shape S hG.l_odd hM f (hT.1 f hf)).2 f' (hT.1 f' hf').1 ⟨g, fun x hx => by
      rw [D.η_ker, ← range_galEmb] at hx
      obtain ⟨y, rfl⟩ := hx
      exact (congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (hg y))).symm⟩
    exact hTo f hf f' hf' s hs
  refine ⟨ne_top_of_le_ne_top hlen hV, T.image ρ, fun x hx => ?_, fun x hx x' hx' h => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    exact hadm f (hT.1 f hf)
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hx'
    rw [hinj f hf f' hf' h]
  · rw [Finset.sum_image fun f hf f' hf' h => hinj f hf f' hf' ⟨1, fun s => by rw [h, one_mul, inv_one, mul_one]⟩]
    simp only [← htr]
    exact (Chr.nrm_mono l hV hlen).trans hle
theorem UpperTheory.V.Z.J.oneCharU_of_katoTwoW_rig_admI_automorphy :
    U3.CohInp → LemmaM → LemmaM' → LemmaP → _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW → _root_.UpperTheory.V.Th.RigidityFirstCase → _root_.UpperTheory.V.Th.RigiditySecondCase → _root_.UpperTheory.V.Z.J.AdmI_s → _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt → _root_.UpperTheory.V.Z.J.OneCharU_s := by
  intro hC hLM hLM' hLP hK hRI hRII hAd hA Ω _ _ _ K _ _ _ _ _ l _ c N _ e ψ hG ι σ t ht hne
  have hunram : ∃ (c' : Coef l) (ψ' : DirichletCharacter c'.O N), eO l c'.O = 1 ∧
      ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) = ((ψ' a : c'.O) : PadicAlgCl l) := by
    classical
    have : NeZero (orderOf ψ) := ⟨fun h => hG.ord (h ▸ dvd_zero l)⟩
    obtain ⟨c', he, _⟩ := (coefSup l).2.1 (orderOf ψ) hG.ord
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot c'.O (orderOf ψ)
    have hζ' : IsPrimitiveRoot (ζ : PadicAlgCl l) (orderOf ψ) :=
      hζ.map_of_injective (f := c'.O.val) Subtype.val_injective
    have hmem : ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) ∈ c'.O := by
      intro a
      by_cases ha : IsUnit a
      · obtain ⟨u, rfl⟩ := ha
        have hp : ψ u ^ orderOf ψ = 1 := by
          rw [← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
        have hp' : ((ψ u : c.O) : PadicAlgCl l) ^ orderOf ψ = 1 := by
          rw [← SubmonoidClass.coe_pow, hp]
          rfl
        obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hp'
        rw [← hi]
        exact pow_mem ζ.2 i
      · rw [ψ.map_nonunit ha]
        exact zero_mem _
    refine ⟨c', ⟨⟨⟨fun a => ⟨_, hmem a⟩, Subtype.ext ?_⟩, fun a b => Subtype.ext ?_⟩,
      fun a ha => Subtype.ext ?_⟩, he, fun _ => rfl⟩
    · show ((ψ 1 : c.O) : PadicAlgCl l) = 1
      rw [map_one]
      rfl
    · show ((ψ (a * b) : c.O) : PadicAlgCl l) = _
      rw [map_mul]
      rfl
    · show ((ψ a : c.O) : PadicAlgCl l) = 0
      rw [ψ.map_nonunit ha]
      rfl
  obtain ⟨c', ψ', he, hψ⟩ := hunram
  have hgd {O O' : Type} [CommRing O] [CommRing O'] (f : O →+* O')
      (hf : Function.Injective f) (χ : DirichletCharacter O N) :
      GD Ω K l e (χ.ringHomComp f) ↔ GD Ω K l e χ := by
    let F : DirichletCharacter O N →* DirichletCharacter O' N := MulChar.ringHomCompHom f
    have hF : Function.Injective F := MulChar.injective_ringHomComp hf
    have hord : orderOf (F χ) = orderOf χ := orderOf_injective F hF χ
    have hcomp (r : ℕ) (ξ : DirichletCharacter O N) : F (HV.comp r ξ) = HV.comp r (F ξ) := by
      ext u
      simp [F, HV.comp, MulChar.ringHomComp_apply]
    have hine : HV.comp l (F χ) ^ 2 = 1 ↔ HV.comp l χ ^ 2 = 1 := by
      rw [← hcomp, ← map_pow, map_eq_one_iff F hF]
    have hpar : PsiEven e (F χ) ↔ PsiEven e χ := by
      change f (χ (-1)) = (-1 : O') ^ e ↔ χ (-1) = (-1 : O) ^ e
      rw [show (-1 : O') ^ e = f ((-1) ^ e) by simp, hf.eq_iff]
    have hchi : F (chiP l χ) = chiP l (F χ) := by
      simp only [chiP, th0, lPrime, lPart, map_mul, map_inv, map_pow, hord, hcomp]
    have hker : (Chr.dirG ℚ Ω (chiP l (F χ))).ker = (Chr.dirG ℚ Ω (chiP l χ)).ker := by
      rw [← hchi]
      ext g
      simp only [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply]
      rw [Units.ext_iff, Units.ext_iff]
      simp only [MulChar.coe_toUnitHom, F, MulChar.ringHomCompHom_apply, MulChar.ringHomComp_apply,
        Units.val_one, ← map_one f, hf.eq_iff]
    change GD Ω K l e (F χ) ↔ GD Ω K l e χ
    constructor
    · intro h
      exact ⟨h.l_odd, h.e_pos, h.N_even, by simpa only [hord] using h.ord, hine.1 h.ine,
        hpar.1 h.par, h.quad, h.imag, h.l_cop, h.cop, by simpa only [hker] using h.eta, h.gen⟩
    · intro h
      exact ⟨h.l_odd, h.e_pos, h.N_even, by simpa only [hord] using h.ord, hine.2 h.ine,
        hpar.2 h.par, h.quad, h.imag, h.l_cop, h.cop, by simpa only [hker] using h.eta, h.gen⟩
  have h1 : ψ.ringHomComp c.O.val.toRingHom = ψ'.ringHomComp c'.O.val.toRingHom :=
    MulChar.ext' hψ
  have hG' : GD Ω K l e ψ' :=
    (hgd c'.O.val.toRingHom Subtype.val_injective ψ').1
      (h1 ▸ (hgd c.O.val.toRingHom Subtype.val_injective ψ).2 hG)
  obtain ⟨h2, h3⟩ := coefIndep Ω l c c' N e ψ ψ' hψ
  have h4 : ∀ g, Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g) =
      Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ') g) := by
    intro g
    simp only [Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow]
    congr 1
    exact Units.ext (hψ _)
  have h5 := congrArg Units.val (h4 (galEmb ℚ K Ω σ))
  have h6 := congrArg (fun u : (PadicAlgCl l)ˣ => (u⁻¹).val) (h4 (galEmb ℚ K Ω σ))
  rw [Ne, h2, h3]
  refine oneChar_unramU hC hLM hLM' hLP hK hRI hRII hAd hA Ω K l c' N e ψ' he hG' ι σ t ?_ hne
  rw [ht, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_one, map_one]
  exact congrArg₂ (· + ·) (congrArg (· + 1) h5) h6
end
