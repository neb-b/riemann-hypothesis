module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.LieNormSquareOfFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

open GlobalTheory.CompanionTheory.Ar.Fl.lie_norm_square_of_family

theorem lie_norm_square_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (σ : R →+* ℂ) (κ : OK H →+* ℂ) (r : ℝ) (n : ℕ) (a : Fin n → L) (u : Fin n → (epsAt (spMap σ) ⟶ T.t.G)), IsFam C T h L ψ → κ (wK H) = σ ω → IsLieNormSq C.P C.v σ r → (∀ k, (u k).left = spMap (dualMap σ) ≫ C.v.left ≫ (ψ (a k)).left) → IsHodgeGram T.t.G T.t.PP.L (spMap σ) u (Matrix.of fun k k' => r * κ (h (a k) (a k'))) := by
  intro E _ _ _ H D R _ ω C T h L ψ σ κ r n a u hF hκ hr hu
  obtain ⟨hlin, -, -, hlam⟩ := hF
  obtain ⟨P', φ, v', uC, Hm, χ, w, ⟨hg', hpb, hLB⟩, hvo, hAH, hdw, hrr⟩ := hr
  have laws := abelianSchemeLaws_all.1
  obtain ⟨Q, ψQ, hQg, hQpb, hQLB⟩ := exists_isPolFibre laws.polBaseChange σ T.pol
  obtain ⟨rig0, hrig0⟩ := P'.rigid
  obtain ⟨u0, Hm0, χ0, -, hAH0, -, -, d20, hend0, -⟩ := thetaUnifAV_all P' rig0 hrig0
  obtain ⟨rigT, hrigT⟩ := Q.rigid
  obtain ⟨uT, HmT, χT, -, hAHT, -, -, d2T, -, -⟩ := thetaUnifAV_all Q rigT hrigT
  have := T.t.comm
  have := C.P.isAb.comm
  have hψm : ∀ b, IsMonHom (ψ b) := fun b => (hlin b).isMonHom
  choose f hfm hfc using fun b : L => @PairingFibre.exists_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hpb hQpb (ψ b) (hψm b)
  choose e hem hec using fun c : OK H =>
    @PairingFibre.exists_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hpb hpb (C.act.act c) (C.act.hom c)
  choose F hFl using fun b : L => @HodgeUnique.exists_linear_compare _ _ _ _ _ _ _ _ uT u0 (f b) (hfm b)
  choose G hGl using fun c : OK H => hend0 (e c) (hem c)
  obtain ⟨K, hK⟩ := @HodgeUnique.exists_linear_compare _ _ _ _ _ _ _ _ u0 uC (𝟙 P'.A) inferInstance
  have hv'T : IsTangent v' := IsVecOver.isTangent hpb hvo (C.basis.1 0)
  have hd0 : u0.IsDiff (K w) v' := by
    simpa using HodgeUniq.isDiff_comp u0 uC d20 (𝟙 P'.A) K hK hv'T hdw
  have hKH : ∀ z z', hermForm Hm0 (K z) (K z') = hermForm Hm z z' :=
    (_root_.GlobalTheory.CM.weilEq_iff_hermForm_eq thetaUnifAV_all laws P' P' P' P' uC uC u0 uC Hm0 Hm χ0 χ hAH0 hAH (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
      K K LinearMap.id LinearMap.id hK hK (fun z => by simp) (fun z => by simp)).1 (fun _ _ _ _ _ _ _ => Iff.rfl)
  have hkey : ∀ b b' : L, ∀ z z', hermForm HmT (F b z) (F b' z') = hermForm Hm0 (G (h b b') z) z' := by
    intro b b' z z'
    have W0 := (PairingFibre.lamEq_weilEq_over_ring laws R C.P C.P T.pol C.P (ψ b) (ψ b') (C.act.act (h b b'))
      (𝟙 _) (hψm b) (hψm b') (C.act.hom _) inferInstance ℂ σ).1 (hlam b b')
    have W1 := (PairingFibre.weilEq_iff hpb hpb hQpb hpb T.t.PP.isLB C.P.isLB Q.isLB P'.isLB (LBIso.symm hQLB)
      (LBIso.symm hLB) (hfc b) (hfc b') (hec (h b b'))
      (show (𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ = φ ≫ (𝟙 C.P.A : C.P.A ⟶ C.P.A).left by simp) (𝟙 (Sp ℂ))).2 (by rw [Category.id_comp]; exact W0)
    have := (_root_.GlobalTheory.CM.weilEq_iff_hermForm_eq thetaUnifAV_all laws P' P' Q P' u0 u0 uT u0 HmT Hm0 χT χ0 hAHT hAH0 (f b) (f b')
      (e (h b b')) (𝟙 _) (F b) (F b') (G (h b b')) LinearMap.id (hFl b) (hFl b') (hGl _) (fun z => by simp)).1 W1 z z'
    simpa using this
  have hg1 : P'.g = 1 := hg'.trans C.dim
  choose c hc using fun x : OK H => CurveAdjoint.exists_scalar hg1 (G x)
  have pa : ∀ (b : OK H) (p : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A),
      Geo.Tor.pushHom hpb _ (p ≫ e b) = Geo.Tor.pushHom hpb _ p ≫ C.act.act b := fun b p =>
    Over.OverMorphism.ext (by
      show (p.left ≫ _) ≫ _ = (p.left ≫ _) ≫ _
      rw [Category.assoc, hec, Category.assoc])
  have inj : ∀ p q : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A, Geo.Tor.pushHom hpb _ p = Geo.Tor.pushHom hpb _ q → p = q :=
    fun p q e' => SymBaseChange.pushPt_injective hpb e'
  have sc : ∀ (b : OK H) (s : ℂ) (Gs : (Fin P'.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z, Gs z = s • z) →
      (∀ z, u0.ex (G b z) = u0.ex (Gs z)) → c b = s := fun b s Gs hG hh => by
    have e' := congrFun ((hc b 1).symm.trans ((LinearMap.congr_fun (CurveAdjoint.linear_eq_of_ex u0 _ _ hh) 1).trans
      (hG 1))) ⟨0, by omega⟩
    simpa using e'
  let j : OK H →+* ℂ := RingHom.mk'
    { toFun := c
      map_one' := sc 1 1 LinearMap.id (fun z => by simp) fun z => inj _ _ (by
        rw [hGl, pa, C.act.one, Category.comp_id, LinearMap.id_apply])
      map_mul' := fun b b' => sc _ _ (G b' ∘ₗ G b) (fun z => by
        rw [LinearMap.comp_apply, hc, hc, smul_smul, mul_comm]) fun z => inj _ _ (by
          rw [LinearMap.comp_apply, hGl, hGl, hGl, pa, pa, pa, C.act.mul, Category.assoc]) }
    fun b b' => sc _ _ (G b + G b') (fun z => by
      rw [LinearMap.add_apply, hc, hc, ← add_smul]; rfl) fun z => inj _ _ (by
        rw [LinearMap.add_apply, u0.ex_add, map_mul, hGl, hGl, hGl, pa, pa, pa, C.act.add, Hom.mul_def, Hom.mul_def,
          ← Category.assoc, comp_lift])
  have hj : ∀ x, j x = c x := fun _ => rfl

  have heig : C.v ≫ C.act.act (wK H) = CMCurveTest.scaleVec ω C.v := by
    obtain ⟨u_, hu_, hprod⟩ := C.eig
    rw [hprod]
    apply Over.OverMorphism.ext
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one]
    exact hu_ 0
  have hover : IsVecOver σ φ (C.v ≫ C.act.act (wK H)) (v' ≫ e (wK H)) := by
    show (v' ≫ e _).left ≫ φ = _
    rw [Over.comp_left, Category.assoc, hec, ← Category.assoc, hvo, Over.comp_left, Category.assoc]
  have hsc : IsVecOver σ φ (C.v ≫ C.act.act (wK H)) (CMCurveTest.scaleVec (σ ω) v') := by
    rw [heig]; exact CMCurveTest.isVecOver_scaleVec hvo ω
  have hvv : v' ≫ e (wK H) = CMCurveTest.scaleVec (σ ω) v' :=
    (existsUnique_isVecOver hpb.1 (C.v ≫ C.act.act (wK H))).unique hover hsc
  have hGw : G (wK H) (K w) = σ ω • K w := by
    haveI := hem (wK H)
    have h1 := HodgeUniq.isDiff_comp u0 u0 d20 (e (wK H)) (G (wK H)) (hGl _) hv'T hd0
    have h2 := CMCurveTest.isDiff_scaleVec u0 hd0 (σ ω)
    rw [← hvv] at h2
    exact HodgeUnique.eq_of_isDiff u0 (isTangent_comp hv'T (e (wK H))) h1 h2
  have hjk : K w ≠ 0 → ∀ x, c x = κ x := by
    intro hne x
    have hw : c (wK H) = σ ω := by
      have e' : (c (wK H) - σ ω) • K w = 0 := by rw [sub_smul, ← hc, hGw, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 e').resolve_right hne)
    obtain ⟨⟨m, k⟩, hx, -⟩ := existsUnique_coord H x
    rw [← hj, hx]
    rw [j.map_add, κ.map_add, j.map_mul, κ.map_mul]
    simp only [map_intCast]
    rw [hj, hw, hκ]
  refine ⟨Q, ψQ, fun k => v' ≫ f (a k), uT, HmT, χT, fun k => F (a k) (K w), hQpb, hQLB, hAHT,
    fun k => ⟨?_, ?_⟩, fun k k' => ?_⟩
  · rw [Over.comp_left, Category.assoc, hfc, ← Category.assoc, hvo, hu k, Category.assoc]
    rfl
  · haveI := hfm (a k)
    exact HodgeUniq.isDiff_comp uT u0 d2T (f (a k)) (F (a k)) (hFl _) hv'T hd0
  · simp only [Matrix.of_apply]
    rw [hkey, hc, hermForm_smul_left, hKH]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, hermForm Hm w w = t := ⟨_, hermForm_self_eq_re hAH.1 w⟩
    rw [ht] at hrr ⊢
    simp only [Complex.ofReal_re] at hrr
    by_cases hne : K w = 0
    · have h0 : (t : ℂ) = 0 := by rw [← ht, ← hKH, hne]; simp [hermForm]
      have h0' : t = 0 := by exact_mod_cast h0
      rw [hrr, h0']
      simp
    · rw [hjk hne, hrr]
      push_cast
      ring

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.PrincipalRootReZeroImSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem principal_root_re_zero_im_sq : H.rt0.re = 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
  simp [sq] at h1 h2
  by_contra h0
  have : H.rt0.im = 0 := by
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left h0
  rw [this] at h1
  nlinarith [mul_self_nonneg H.rt0.re]

theorem rt0_conj_neg_ne_zero : conj H.rt0 = -H.rt0 := by
  apply Complex.ext <;> simp [principal_root_re_zero_im_sq (H := H)]

theorem conjugate_rt (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ (H.rt : E) = H.rt0 ↔ σ (H.rt : E) ≠ H.rt0 := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases rt_cases (H := H) σ with h | h
  · rw [h, rt0_conj_neg_ne_zero]
    simp only [ne_eq, not_true_eq_false, iff_false]
    exact fun e => Host_rt0_ne_neg (H := H) e.symm
  · rw [h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    simp only [true_iff]
    exact fun e => Host_rt0_ne_neg (H := H) e.symm

theorem sum_split {M : Type} [AddCommMonoid M] (F : (E →+* ℂ) → M) :
    ∑ σ, F σ = ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), F σ +
      ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), F (ComplexEmbedding.conjugate σ) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0)]
  congr 1
  refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact (conjugate_rt σ).2 hσ
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact fun h' => ((conjugate_rt σ).1 h') hσ
  · intro σ _; ext x; simp
  · intro σ _; ext x; simp
  · intro σ _; simp

theorem emb_indep (l : (E →+* ℂ) → ℂ) (h : ∀ b : 𝓞 E, ∑ σ, l σ * σ (b : E) = 0) : l = 0 := by
  let F : (E →+* ℂ) → (𝓞 E →* ℂ) := fun σ => (σ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hF : Function.Injective F := by
    intro σ σ' e
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext b
    exact DFunLike.congr_fun e b
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp F hF
  funext σ
  refine Fintype.linearIndependent_iff.1 li l ?_ σ
  funext b
  simpa [F, Finset.sum_apply] using h b

theorem exists_big (a : 𝓞 E) (ha : a ≠ 0) (b : Bool) :
    ∃ σ : E →+* ℂ, σ (H.rt : E) = (if b then H.rt0 else -H.rt0) ∧ 1 ≤ ‖σ (a : E)‖ := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ σ : E →+* ℂ, ‖σ (a : E)‖ < 1 := by
    intro σ
    by_cases hσ : σ (H.rt : E) = (if b then H.rt0 else -H.rt0)
    · exact hcon σ hσ
    · have h2 : ComplexEmbedding.conjugate σ (H.rt : E) = (if b then H.rt0 else -H.rt0) := by
        rw [ComplexEmbedding.conjugate_coe_eq]
        rcases rt_cases (H := H) σ with h | h <;> cases b <;>
          simp_all [rt0_conj_neg_ne_zero (H := H)]
      have := hcon _ h2
      rwa [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at this
  obtain ⟨σ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hlt : ∏ σ : E →+* ℂ, ‖σ (a : E)‖ < 1 := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ₀)]
    have h1 : ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (a : E)‖ ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun σ _ => (hall σ).le)
    calc ‖σ₀ (a : E)‖ * ∏ σ ∈ Finset.univ.erase σ₀, ‖σ (a : E)‖ ≤ ‖σ₀ (a : E)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ < 1 := by rw [_root_.mul_one]; exact hall σ₀
  have hge : 1 ≤ ∏ σ : E →+* ℂ, ‖σ (a : E)‖ := by
    have hN : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
    have e1 := Algebra.norm_eq_prod_embeddings ℚ ℂ (a : E)
    rw [← Algebra.coe_norm_int] at e1
    have e2 : ∏ τ : E →ₐ[ℚ] ℂ, τ (a : E) = ∏ σ : E →+* ℂ, σ (a : E) :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun τ => rfl)
    rw [e2] at e1
    rw [← norm_prod, ← e1]
    have : ((algebraMap ℚ ℂ) ((Algebra.norm ℤ a : ℤ) : ℚ)) = ((Algebra.norm ℤ a : ℤ) : ℂ) := by simp
    rw [this, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hN
  linarith

end PositivityTheory.Xgf.DPer

end
end

