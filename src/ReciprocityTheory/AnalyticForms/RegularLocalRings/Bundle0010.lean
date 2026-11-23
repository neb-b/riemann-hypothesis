module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0009
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.Immersion
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem AlgRes.fderiv_affCoord_ker_eq_bot {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A) (i : Fin R.n)
    (x : R.M) (hx : x ∈ R.src i) (hxD : (fun q => eval (R.coord i x) (R.lift i q)) ∉ conePts D)
    (p : (k : K) → ι k) (hp : ∀ k, eval (R.coord i x) (R.lift i ⟨k, p k⟩) ≠ 0)
    (j : Fin A.n) (hj : x ∈ (A.chart j).source) :
    (fderiv ℂ (fun y => affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)))
      (A.chart j x)).ker = ⊥ := by
  classical
  have hy0t : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hj
  have hsy0 : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  set f : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y => affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)) with hfdef
  obtain ⟨O, hO, hxO, -, q, F, hOF⟩ := R.inv i x hx hxD p hp
  obtain ⟨ψ, hψc, hxψ, hψs, hψ⟩ :=
    hA.2 i x hx (R.sncAt i x hx).r (R.sncAt i x hx).span_eq O hO hxO
  set r := (R.sncAt i x hx).r with hr
  have hw0 : f (A.chart j x) = affCoord p (fun q => eval (R.coord i x) (R.lift i q)) := by
    simp only [f, hsy0]
  have hqw0 : eval (f (A.chart j x)) q ≠ 0 := by rw [hw0]; exact (hOF x hxO).2.1
  let H : ((Σ k, ι k) → ℂ) → Fin (R.amb i) → ℂ := fun w l => eval w (F l) / eval w q
  let G : ((Σ k, ι k) → ℂ) → Fin e → ℂ := fun w => (A.chart j ∘ ψ.symm) (evalFam r (H w))
  have hHx : ∀ y ∈ O, H (affCoord p fun q => eval (R.coord i y) (R.lift i q)) = R.coord i y := by
    intro y hy; funext l; simp only [H]; rw [div_eq_iff (hOF y hy).2.1]; exact ((hOF y hy).2.2 l).symm
  have hH0 : H (f (A.chart j x)) = R.coord i x := by rw [hw0]; exact hHx x hxO
  have hHan : AnalyticAt ℂ H (f (A.chart j x)) := by
    rw [analyticAt_pi_iff]; intro l
    exact (AnalyticOnNhd.eval_mvPolynomial (F l) _ (Set.mem_univ _)).div
      (AnalyticOnNhd.eval_mvPolynomial q _ (Set.mem_univ _)) hqw0
  have hEan : AnalyticAt ℂ (evalFam r) (H (f (A.chart j x))) := by
    rw [analyticAt_pi_iff]; intro l
    exact AnalyticOnNhd.eval_mvPolynomial (r l) _ (Set.mem_univ _)
  have hTan : AnalyticAt ℂ (A.chart j ∘ ψ.symm) (evalFam r (H (f (A.chart j x)))) := by
    rw [hH0, ← hψ x hxψ]
    refine (hψc j).2 (ψ x) ⟨ψ.map_source hxψ, ?_⟩
    show ψ.symm (ψ x) ∈ (A.chart j).source
    rw [ψ.left_inv hxψ]; exact hj
  have hGd : DifferentiableAt ℂ G (f (A.chart j x)) :=
    DifferentiableAt.comp (g := A.chart j ∘ ψ.symm) (f := evalFam r ∘ H) (f (A.chart j x))
      hTan.differentiableAt
      (DifferentiableAt.comp (f (A.chart j x)) hEan.differentiableAt hHan.differentiableAt)
  have hfd : DifferentiableAt ℂ f (A.chart j x) := by
    rw [differentiableAt_pi]; intro q'
    have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.src i :=
      ⟨hy0t, by show (A.chart j).symm (A.chart j x) ∈ R.src i; rw [hsy0]; exact hx⟩
    have h1 := hA.1 i (R.lift i q') j (A.chart j x) hmem
    have h2 := hA.1 i (R.lift i ⟨q'.1, p q'.1⟩) j (A.chart j x) hmem
    have hne : ((fun y => eval (R.coord i y) (R.lift i ⟨q'.1, p q'.1⟩)) ∘ (A.chart j).symm)
        (A.chart j x) ≠ 0 := by
      simp only [Function.comp, hsy0]; exact hp q'.1
    exact (h1.div h2 hne).differentiableAt
  have hev : (G ∘ f) =ᶠ[𝓝 (A.chart j x)] id := by
    have h1 : ∀ᶠ y in 𝓝 (A.chart j x), y ∈ (A.chart j).target :=
      (A.chart j).open_target.mem_nhds hy0t
    have h2 : ∀ᶠ y in 𝓝 (A.chart j x), (A.chart j).symm y ∈ ψ.source :=
      ((A.chart j).continuousAt_symm hy0t).preimage_mem_nhds
        (ψ.open_source.mem_nhds (by rw [hsy0]; exact hxψ))
    filter_upwards [h1, h2] with y hy1 hy2
    have hy'O : (A.chart j).symm y ∈ O := (hψs hy2).1
    show (A.chart j) (ψ.symm (evalFam r (H (f y)))) = y
    have hfy : f y = affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)) := rfl
    rw [hfy, hHx _ hy'O, ← hψ _ hy2, ψ.left_inv hy2, (A.chart j).right_inv hy1]
  have hcomp := hGd.hasFDerivAt.comp (A.chart j x) hfd.hasFDerivAt
  have huniq := hcomp.unique ((hasFDerivAt_id (A.chart j x)).congr_of_eventuallyEq hev)
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
  have hv' : fderiv ℂ f (A.chart j x) v = 0 := hv
  rw [← this, hv', map_zero]

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA
section
namespace ReciprocityTheory.AnForm.R.WMult

open AlgebraicGeometry CategoryTheory IsLocalRing

variable {W : Scheme.{0}}

theorem stalkId_eq_map_germ (I : W.IdealSheafData) (y : W) (U : W.affineOpens) (hy : y ∈ U.1) :
    FinalTheorems.stalkId I y = Ideal.map (W.presheaf.germ U.1 y hy).hom (I.ideal U) := by
  have key : ∀ (V V' : W.affineOpens) (h : V' ≤ V) (hyV' : y ∈ V'.1),
      Ideal.map (W.presheaf.germ V.1 y ((show V'.1 ≤ V.1 from h) hyV')).hom (I.ideal V) =
        Ideal.map (W.presheaf.germ V'.1 y hyV').hom (I.ideal V') := by
    intro V V' h hyV'
    rw [← I.map_ideal h, Ideal.map_map]
    congr 1
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (W.presheaf.germ_res (homOfLE (show V'.1 ≤ V.1 from h)) y hyV').symm
  rw [FinalTheorems.stalkId]
  apply le_antisymm
  · refine iSup₂_le fun V hyV => ?_
    obtain ⟨f, g, hfg, hyf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hy, hyV⟩
    have hWU : W.affineBasicOpen f ≤ U := W.basicOpen_le f
    have hWV : W.affineBasicOpen f ≤ V := by
      show W.basicOpen f ≤ V.1
      rw [hfg]
      exact W.basicOpen_le g
    rw [key V _ hWV hyf, key U _ hWU hyf]
  · exact le_iSup₂ (f := fun (V : W.affineOpens) (hV : y ∈ V.1) =>
      Ideal.map (W.presheaf.germ V.1 y hV).hom (I.ideal V)) U hy

theorem mem_support_fromSpec_iff (I : W.IdealSheafData) (U : W.affineOpens) (hU : IsAffineOpen U.1)
    (P : PrimeSpectrum Γ(W, U.1)) :
    hU.fromSpec P ∈ (I.support : Set W) ↔ I.ideal U ≤ P.asIdeal := by
  have hmem : hU.fromSpec P ∈ U.1 := by
    have hr : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  show hU.fromSpec P ∈ I.support ↔ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  exact (Set.ext_iff.1 (hU.fromSpec_preimage_zeroLocus (I.ideal U : Set Γ(W, U.1))) P).trans
    ((PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe)

private theorem ring_ord_ringEquiv_apply {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (z : A) : Ring.ord B (e z) = Ring.ord A z := by
  have hI : Ideal.comap e (Ideal.span {e z}) = Ideal.span {z} := by
    rw [show Ideal.span {e z} = Ideal.map e (Ideal.span {z}) by rw [Ideal.map_span, Set.image_singleton]]
    exact Ideal.comap_map_of_bijective e e.bijective
  unfold Ring.ord
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  refine Order.krullDim_eq_of_orderIso ?_
  let o3 := Ideal.relIsoOfBijective (e : A →+* B) e.bijective
  have h3 : o3 (Ideal.span {e z}) = Ideal.span {z} := hI
  exact (Submodule.comapMkQRelIso _).trans (((o3.Ici _).trans
    (OrderIso.setCongr _ _ (by rw [h3]))).trans (Submodule.comapMkQRelIso _).symm)

theorem ord_isLocalization_eq_exponent {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ}
    (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S (Ideal.span {f i})] :
    Ring.ord S (algebraMap R S (u * ∏ j ∈ J, f j ^ m j)) = (m i : ℕ∞) := by
  have hL := ord_localization_eq_exponent f hspan hdim J u m i hi
  let e : Localization.AtPrime (Ideal.span {f i}) ≃ₐ[R] S :=
    IsLocalization.algEquiv (Ideal.span {f i}).primeCompl (Localization.AtPrime (Ideal.span {f i})) S
  rw [← e.commutes, ← hL]
  exact ring_ord_ringEquiv_apply e.toRingEquiv _

end ReciprocityTheory.AnForm.R.WMult
end

