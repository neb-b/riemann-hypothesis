module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PEigOf
section
open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open UpperTheory.Gal.CertificateRingHomMap Module

private lemma common_eig {M J : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (S : J → End ℂ M) (hS : ∀ i j, S i * S j = S j * S i) (θ : J → ℂ) (y : M) (hy : y ≠ 0)
    (hG : ∀ j, y ∈ (S j).maxGenEigenspace (θ j)) : ∃ x : M, x ≠ 0 ∧ ∀ j, S j x = θ j • x := by
  let G : Submodule ℂ M := ⨅ j, (S j).maxGenEigenspace (θ j)
  have hyG : y ∈ G := (Submodule.mem_iInf _).2 hG
  have hGne : G ≠ ⊥ := fun h => hy (by rw [h] at hyG; simpa using hyG)
  have hst : ∀ j, ∀ x ∈ G, S j x ∈ G := by
    intro j x hx
    refine (Submodule.mem_iInf _).2 fun i => ?_
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (show Commute (S i) (S j) from hS i j) (θ i)
      ((Submodule.mem_iInf _).1 hx i)
  obtain ⟨v, hvG, hv0, hv⟩ := UpperTheory.V.LinAlg.simEig S hS _ G rfl hGne hst
  refine ⟨v, hv0, fun j => ?_⟩
  obtain ⟨c, hc⟩ := hv j
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hvG j)
  have h1 : (S j - θ j • (1 : End ℂ M)) v = (c - θ j) • v := by
    simp [hc, sub_smul]
  have hp : ∀ n : ℕ, ((S j - θ j • (1 : End ℂ M)) ^ n) v = (c - θ j) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_apply_eq_comp, h1, map_smul, ih, smul_smul, pow_succ']
  rw [hp] at hk
  rcases smul_eq_zero.1 hk with h | h
  · have : c = θ j := sub_eq_zero.1 (by_contra fun h' => pow_ne_zero k h' h)
    rw [hc, this]
  · exact absurd h hv0

private lemma wop_restrict {M J : Type} [AddCommGroup M] [Module ℂ M] (U : Submodule ℂ M)
    (T : J → End ℂ M) (h : ∀ j, ∀ x ∈ U, T j x ∈ U) (s : List J →₀ ℂ) (x : U) :
    ((wop (fun j => (T j).restrict (h j)) s x : U) : M) = wop T s (x : M) := by
  have hw : ∀ (w : List J) (x : U),
      (((w.map fun j => (T j).restrict (h j)).prod x : U) : M) = (w.map T).prod (x : M) := by
    intro w
    induction w with
    | nil => intro x; simp
    | cons j w ih =>
      intro x
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, LinearMap.coe_restrict_apply, ih]
  unfold wop
  simp only [Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
    Submodule.coe_smul, hw]

end UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.eigOf_of :
    UpperTheory.Gal.CertificateRingHomMap.ProjOne.{0} → EigOf := by
  open UpperTheory.Gal.CertificateRingHomMap Module in
  intro hP B J _ W _ _ _ T u θ hc
  let U : ∀ b, Submodule ℂ (W b) := fun b =>
    Submodule.span ℂ {x | ∃ (w : List J) (z : W b), x = ((w.map (T b)).prod * u b) z}
  have hst : ∀ b j, ∀ x ∈ U b, T b j x ∈ U b := by
    intro b j x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨w, z, rfl⟩ := h
      exact Submodule.subset_span ⟨j :: w, z, by simp [mul_apply_eq_comp]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hcm : ∀ b j j', ∀ x ∈ U b, T b j (T b j' x) = T b j' (T b j x) := by
    intro b j j' x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨w, z, rfl⟩ := h
      have := LinearMap.congr_fun (hc b j j' w) z
      simpa [mul_apply_eq_comp] using this
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul a x _ hx => simp only [map_smul, hx]
  let S : ∀ b, J → End ℂ (U b) := fun b j => (T b j).restrict (hst b j)
  have hS : ∀ b j j', S b j * S b j' = S b j' * S b j := by
    intro b j j'
    ext ⟨x, hx⟩
    exact hcm b j j' x hx
  let T' : J → ∀ b, End ℂ (U b) := fun j b => S b j
  cases nonempty_fintype B
  obtain ⟨s, h1, -, h3⟩ := hP ℂ (∀ b, End ℂ (U b)) J T' (fun i j => funext fun b => hS b i j) θ
  refine ⟨s, h1, fun b hne => ?_⟩
  have hev : (wop T' s) b = wop (S b) s := map_wop (Pi.evalAlgHom ℂ (fun b => End ℂ (U b)) b) T' s
  obtain ⟨z, hz⟩ : ∃ z, (wop (T b) s * u b) z ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  have hu : u b z ∈ U b := Submodule.subset_span ⟨[], z, by simp⟩
  have hcoe : ((wop (S b) s ⟨u b z, hu⟩ : U b) : W b) = wop (T b) s (u b z) :=
    wop_restrict (U b) (T b) (hst b) s ⟨u b z, hu⟩
  have hy : wop (S b) s ⟨u b z, hu⟩ ≠ 0 := by
    intro h
    apply hz
    rw [mul_apply_eq_comp, ← hcoe, h]
    rfl
  have hyG : ∀ j, wop (S b) s ⟨u b z, hu⟩ ∈ (S b j).maxGenEigenspace (θ j) := by
    intro j
    obtain ⟨N, hN⟩ := h3 j
    have hN' := congrArg (Pi.evalAlgHom ℂ (fun b => End ℂ (U b)) b) hN
    rw [map_mul, map_pow, map_sub, AlgHom.commutes, map_zero] at hN'
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨N, ?_⟩
    have h2 : (S b j - θ j • (1 : End ℂ (U b))) ^ N * wop (S b) s = 0 := by
      rw [← hev, Algebra.algebraMap_eq_smul_one] at *
      exact hN'
    have := LinearMap.congr_fun h2 ⟨u b z, hu⟩
    simpa [mul_apply_eq_comp] using this
  obtain ⟨x, hx0, hx⟩ := common_eig (S b) (hS b) θ _ hy hyG
  refine ⟨(x : W b), fun h => hx0 (Subtype.ext h), fun j => ?_⟩
  exact congrArg Subtype.val (hx j)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGroupTop
section
open UpperTheory.Gal.LocalSmoothExtension

private lemma sum_swap {A : Type} (s : Finset A) (a : A → ℂ) (g : A → ℂ → ℂ) (R : Multiset ℂ) :
    (R.map fun μ => ∑ α ∈ s, a α * g α μ).sum = ∑ α ∈ s, a α * (R.map (g α)).sum := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons b R ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, mul_add, Finset.sum_add_distrib]

theorem UpperTheory.Gal.LocalSmoothExtension.groupTop_of :
    GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd → GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace → RootW → InvRoots → InvPolProps → MarkRoots → DPairPol → DSumCongr → TestOf → TestOne → GroupTop := by
  classical
  intro hW hT hR hInv hProps hMark hDP hDS hTest hOne p _ D G L lam i₀ h hh
  have hcj : NumberField.ComplexEmbedding.conjugate (D.tau i₀) ≠ D.tau i₀ := fun e =>
    NumberField.IsTotallyComplex.complexEmbedding_not_isReal (D.tau i₀)
      (NumberField.ComplexEmbedding.isReal_iff.2 e)
  obtain ⟨k₀, hk⟩ := hR D.F G.n (D.tau i₀) (epsOf D) lam h hcj hh
  refine ⟨k₀, fun k hkk => ?_⟩
  obtain ⟨c, hc1, hc2⟩ := hk k hkk
  refine ⟨c, hc1, ?_⟩
  intro ha hga hodd v hv V _ _ _ ξ hξ Lv f hf hG y
  have hTf := hTest _ _ f hf
  have hO := hOne p G
  rw [hW p G hga hodd v hv _ Lv f hTf.1 hG.reg (Kp G) (oneP G) hO.1 hG.pairs]
  have key : ∀ P : GlobalTheory.LKDef.DPair G,
      GlobalTheory.RootSumWeights.rootSum G v (fun P μ => c.sum fun α r => r * cW L i₀ v α y P μ) P.pol =
        (fun P => schW lam (endPol L P)) P.pol * ∑ i, y ^ h i := by
    intro P
    obtain ⟨h0, q, hq⟩ := hDP p G P v
    have hroots := hMark p D G L ha i₀ v hv hInv P.pol h0
    have h0' : (P.pol.map (L.e.symm : G.F →+* D.F)).coeff 0 ≠ 0 := by
      rw [Polynomial.coeff_map]
      exact (map_ne_zero _).2 h0
    obtain ⟨d1, d2, d3⟩ := hProps D.F (P.pol.map (L.e.symm : G.F →+* D.F)) h0'
    have hdeg : (endPol L P.pol).natDegree = G.n := by
      show (invPol _).natDegree = _
      rw [d1, Polynomial.natDegree_map]
      exact P.reg.1
    have hsep : (endPol L P.pol).Separable := d3 (P.reg.2.map)
    have habs : ∃ q : ℝ, ∀ z ∈ UpperTheory.Gal.W2.rts (endPol L P.pol) (D.tau i₀),
        z * (starRingEnd ℂ) z = q := by
      refine ⟨q⁻¹, fun z hz => ?_⟩
      rw [← hroots, Multiset.mem_map] at hz
      obtain ⟨μ, hμ, rfl⟩ := hz
      have hm := hq μ hμ
      have hq' : ((q⁻¹ : ℝ) : ℂ) = (μ * (starRingEnd ℂ) μ)⁻¹ := by
        rw [hm]; push_cast; rfl
      rw [hq']
      unfold markOf
      split_ifs
      · rw [map_inv₀, mul_inv]
      · rw [map_inv₀, Complex.conj_conj, mul_inv, mul_comm]
    have := hc2 (endPol L P.pol) hdeg hsep d2 habs y
    show _ = schW lam (endPol L P.pol) * _
    rw [← this]
    unfold GlobalTheory.RootSumWeights.rootSum
    simp only [Finsupp.sum]
    rw [sum_swap]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← hroots, Multiset.map_map]
    rfl
  rw [hDS p G _ (fun P => schW lam (endPol L P)) (∑ i, y ^ h i) key Lv.K.toSubgroup f 1 (Kp G) (oneP G)]
  rw [hT p G hga V ξ (fun P => schW lam (endPol L P)) hξ Lv f hTf.1 hTf.2 (Kp G) (oneP G) hO.1 hO.2 hG.forms]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHeckeTraceSemi
section
open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.LKDef

section Transport

variable {Γ H V V' : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V']

private theorem symm_semi {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e) :
    IsSemi σ.symm e.symm := by
  intro c y
  apply e.injective
  rw [hs]
  simp

private theorem symm_int {ξ : Representation ℂ Γ V} {ξ' : Representation ℂ Γ V'} {e : V ≃+ V'}
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) : ∀ g x, e.symm (ξ' g x) = ξ g (e.symm x) := by
  intro g x
  apply e.injective
  rw [hi]
  simp

private theorem forms_left {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    (φ : HeckeTraceForms.forms ι K ξ) (γ : Γ) (g : H) : φ.1 (ι γ * g) = ξ γ (φ.1 g) := φ.2.1 γ g

private theorem forms_right {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    (φ : HeckeTraceForms.forms ι K ξ) (k : H) (hk : k ∈ K) (g : H) : φ.1 (g * k) = φ.1 g := φ.2.2 k hk g

private def fmap (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} (e : V ≃+ V') (hi : ∀ g x, e (ξ g x) = ξ' g (e x))
    (φ : HeckeTraceForms.forms ι K ξ) : HeckeTraceForms.forms ι K ξ' :=
  ⟨fun g => e (φ.1 g), fun γ g => by
      show e (φ.1 (ι γ * g)) = ξ' γ (e (φ.1 g))
      rw [forms_left φ, hi],
    fun k hk g => by
      show e (φ.1 (g * k)) = e (φ.1 g)
      rw [forms_right φ k hk]⟩

private def fequiv (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} (e : V ≃+ V') (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) :
    HeckeTraceForms.forms ι K ξ ≃+ HeckeTraceForms.forms ι K ξ' where
  toFun := fmap ι K e hi
  invFun := fmap ι K e.symm (symm_int hi)
  left_inv φ := by
    apply Subtype.ext; funext g
    exact e.symm_apply_apply _
  right_inv φ := by
    apply Subtype.ext; funext g
    exact e.apply_symm_apply _
  map_add' a b := by
    apply Subtype.ext; funext g
    exact map_add e _ _

private theorem fequiv_semi (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) : IsSemi σ (fequiv ι K e hi) := by
  intro c φ
  apply Subtype.ext; funext g
  exact hs c (φ.1 g)

private theorem transport {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) {F : H → ℂ}
    {T : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] HeckeTraceForms.forms ι K ξ} (hT : HeckeTraceForms.IsHecke ι K ξ F T) :
    ∃ T' : HeckeTraceForms.forms ι K ξ' →ₗ[ℂ] HeckeTraceForms.forms ι K ξ',
      HeckeTraceForms.IsHecke ι K ξ' (fun h => σ (F h)) T' ∧
        ∀ x, fequiv ι K e hi (T x) = T' (fequiv ι K e hi x) := by
  have hsym := symm_semi (fequiv_semi ι K hs hi)
  refine ⟨{ toFun := fun ψ => fequiv ι K e hi (T ((fequiv ι K e hi).symm ψ))
            map_add' := fun a b => by simp
            map_smul' := fun c ψ => by
              rw [hsym c ψ, map_smul, fequiv_semi ι K hs hi]
              simp }, ?_, ?_⟩
  · intro ψ g
    change e ((T ((fequiv ι K e hi).symm ψ)).1 g) = _
    rw [hT, AddEquiv.map_finsum]
    refine finsum_congr fun q => ?_
    rw [hs]
    congr 1
    exact e.apply_symm_apply _
  · intro x
    change fequiv ι K e hi (T x) = fequiv ι K e hi (T ((fequiv ι K e hi).symm (fequiv ι K e hi x)))
    rw [AddEquiv.symm_apply_apply]

private theorem hecke_unique {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {F : H → ℂ}
    {T T' : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] HeckeTraceForms.forms ι K ξ} (h : HeckeTraceForms.IsHecke ι K ξ F T)
    (h' : HeckeTraceForms.IsHecke ι K ξ F T') : T = T' := by
  apply LinearMap.ext; intro φ
  apply Subtype.ext; funext g
  rw [h φ g, h' φ g]

end Transport

theorem heckeTraceSemi_of :
    TraceSemi → HeckeTraceSemi := by
  intro hTr σ Γ H V V' _ _ _ _ _ _ ξ ξ' e hs hi ι K F
  by_cases h : ∃ T, HeckeTraceForms.IsHecke ι K ξ F T
  · obtain ⟨T', hT', hint⟩ := transport (ι := ι) (K := K) hs hi h.choose_spec
    have h' : ∃ T, HeckeTraceForms.IsHecke ι K ξ' (fun x => σ (F x)) T := ⟨T', hT'⟩
    have hc : h'.choose = T' := hecke_unique h'.choose_spec hT'
    rw [HeckeTraceForms.heckeTrace, HeckeTraceForms.heckeTrace, dite_eq_left h, dite_eq_left h', hc]
    exact hTr σ _ _ (fequiv ι K e hi) (fequiv_semi ι K hs hi) _ _ hint
  · have h' : ¬ ∃ T, HeckeTraceForms.IsHecke ι K ξ' (fun x => σ (F x)) T := by
      rintro ⟨T', hT'⟩
      obtain ⟨T, hT, -⟩ := transport (ι := ι) (K := K) (symm_semi hs) (symm_int hi) hT'
      refine h ⟨T, ?_⟩
      simpa only [RingEquiv.symm_apply_apply] using hT
    rw [HeckeTraceForms.heckeTrace, HeckeTraceForms.heckeTrace, dite_eq_right h, dite_eq_right h', map_zero]

end UpperTheory.Gal.LocalSmoothExtension
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PInvPolProps
section
set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

theorem invPolProps_of (hR : InvRoots) : InvPolProps := by
  intro F _ _ P hP
  have hP0 : P ≠ 0 := fun h => hP (by simp [h])
  have hc : (P.coeff 0)⁻¹ ≠ 0 := inv_ne_zero hP
  have hrr : ∀ Q : F[X], Q.coeff 0 ≠ 0 → Q.reverse.reverse = Q := by
    intro Q hQ
    have hQd : Q.reverse.natDegree = Q.natDegree := by
      rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hQ), Nat.sub_zero]
    ext n
    rw [coeff_reverse, hQd, coeff_reverse, revAt_invol]
  have hdeg : P.reverse.natDegree = P.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hP), Nat.sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · unfold invPol
    rw [natDegree_C_mul hc, hdeg]
  · unfold invPol
    rw [mul_coeff_zero, coeff_C_zero, coeff_zero_reverse]
    exact mul_ne_zero hc (leadingCoeff_ne_zero.mpr hP0)
  · intro hs
    unfold invPol
    have hrs : P.reverse.Separable := by
      rw [PerfectField.separable_iff_squarefree]
      intro x hx
      obtain ⟨y, hy⟩ := hx
      have hx0 : x.coeff 0 ≠ 0 := by
        intro h0
        have h1 : P.reverse.coeff 0 = 0 := by
          rw [hy, mul_coeff_zero, mul_coeff_zero, h0, zero_mul, zero_mul]
        rw [coeff_zero_reverse] at h1
        exact leadingCoeff_ne_zero.mpr hP0 h1
      have hPx : x.reverse * x.reverse ∣ P := by
        refine ⟨y.reverse, ?_⟩
        rw [← hrr P hP, hy, reverse_mul_of_domain, reverse_mul_of_domain]
      have hu : IsUnit x.reverse := hs.squarefree _ hPx
      have hxd : x.natDegree = 0 := by
        have h1 : x.reverse.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
        rwa [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hx0), Nat.sub_zero] at h1
      rw [eq_C_of_natDegree_eq_zero hxd]
      exact isUnit_C.mpr (IsUnit.mk0 _ hx0)
    rw [mul_comm]
    exact hrs.mul_unit (isUnit_C.mpr (IsUnit.mk0 _ hc))

end UpperTheory.Gal.LocalSmoothExtension
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PInvRoots
section
open UpperTheory.Gal.LocalSmoothExtension

open Polynomial in
private theorem rev_lin (r : ℂ) (hr : r ≠ 0) :
    (X - C r : ℂ[X]).reverse = C (-r) * (X - C r⁻¹) := by
  have h1 : (C (-r) * (X - C r⁻¹) : ℂ[X]) = 1 - C r * X := by
    rw [mul_sub, ← C_mul]
    simp [hr]
    ring
  rw [h1]
  ext n
  rw [coeff_reverse, natDegree_X_sub_C]
  rcases n with _ | _ | n
  · rw [revAt_le (by norm_num)]
    simp [coeff_X, coeff_C]
  · rw [revAt_le (by norm_num)]
    simp [coeff_X, coeff_C, coeff_one]
  · rw [revAt_eq_self_of_lt (by omega)]
    simp [coeff_X, coeff_one, coeff_C]

open Polynomial in
private theorem rev_prod (s : Multiset ℂ) (hs : ∀ z ∈ s, z ≠ 0) :
    ((s.map (fun a => X - C a)).prod : ℂ[X]).reverse.roots = s.map (fun z => z⁻¹) := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, ← C_1, reverse_C, roots_C, Multiset.map_zero]
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have ih' := ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have hm : ((s.map (fun a => X - C a)).prod : ℂ[X]) ≠ 0 :=
      (monic_multiset_prod_of_monic s _ fun a _ => monic_X_sub_C a).ne_zero
    have hm' : ((s.map (fun a => X - C a)).prod : ℂ[X]).reverse ≠ 0 := by
      simpa [reverse_eq_zero] using hm
    have hl : (C (-a) * (X - C a⁻¹) : ℂ[X]) ≠ 0 :=
      mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr ha)) (X_sub_C_ne_zero _)
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, rev_lin a ha,
      roots_mul (mul_ne_zero hl hm'), roots_C_mul _ (neg_ne_zero.mpr ha), roots_X_sub_C, ih',
      Multiset.map_cons, Multiset.singleton_add]

open Polynomial in
private theorem rev_roots (Q : ℂ[X]) (h0 : Q.coeff 0 ≠ 0) :
    Q.reverse.roots = Q.roots.map (fun z => z⁻¹) := by
  have hQ : Q ≠ 0 := fun h => h0 (by simp [h])
  have hc : Multiset.card Q.roots = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hf := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  have hz : ∀ z ∈ Q.roots, z ≠ 0 := by
    rintro z hz rfl
    exact h0 (by rw [coeff_zero_eq_eval_zero]; exact (mem_roots hQ).mp hz)
  have hl : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  conv_lhs => rw [← hf]
  rw [reverse_mul_of_domain, reverse_C, roots_C_mul _ hl, rev_prod _ hz]

open Polynomial in
theorem UpperTheory.Gal.LocalSmoothExtension.invRoots_of :
    InvRoots := by
  intro F _ _ P h0 τ
  have hτ : τ (P.coeff 0) ≠ 0 := by simpa using h0
  have hmap : (P.map τ).coeff 0 ≠ 0 := by simpa [coeff_map] using h0
  have hrev : (P.reverse).map τ = (P.map τ).reverse := by
    rw [reverse, reverse, natDegree_map, reflect_map]
  have hinv : (invPol P).map τ = C (τ (P.coeff 0))⁻¹ * (P.map τ).reverse := by
    rw [invPol, Polynomial.map_mul, map_C, hrev, map_inv₀]
  simp only [UpperTheory.Gal.W2.rts]
  rw [hinv, roots_C_mul _ (inv_ne_zero hτ), rev_roots _ hmap]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PLefSum
section
set_option autoImplicit false

noncomputable section

open Matrix Polynomial
open UpperTheory.Gal.W2 (lefTerm)

namespace UpperTheory.Gal.LocalSmoothExtension

theorem lefSum_of : LefSum := by
  intro d A y
  set p : ℂ[X] := (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X])).det with hp
  have hdeg : p.natDegree < d + 1 := by
    have h1 : (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X]) : Matrix (Fin d) (Fin d) ℂ[X]) =
        (X : ℂ[X]) • A.map C + (1 : Matrix (Fin d) (Fin d) ℂ).map C := by
      rw [Matrix.map_one C (map_zero _) (map_one _), add_comm]
    have hle := natDegree_det_X_add_C_le A 1
    rw [← h1, Fintype.card_fin] at hle
    exact Nat.lt_succ_of_le hle
  have hev : p.eval (-y) = (1 - y • A).det := by
    rw [hp, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, coe_evalRingHom, smul_eq_mul]
    split_ifs <;> simp <;> ring
  unfold lefTerm
  rw [← hev, eval_eq_sum_range' hdeg, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end UpperTheory.Gal.LocalSmoothExtension
end
end

