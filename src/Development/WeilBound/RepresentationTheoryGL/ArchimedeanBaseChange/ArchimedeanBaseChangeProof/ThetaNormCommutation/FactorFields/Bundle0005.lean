module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PParam
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.ParamP

theorem tw_symm {G : Type} [Group G] (θ : G →* G) {x y : G} (h : ∃ g, x = g⁻¹ * y * θ g) :
    ∃ g, y = g⁻¹ * x * θ g := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  simp only [inv_inv, map_inv]
  group

theorem tw_trans {G : Type} [Group G] (θ : G →* G) {x y z : G} (h₁ : ∃ g, x = g⁻¹ * y * θ g)
    (h₂ : ∃ g, y = g⁻¹ * z * θ g) : ∃ g, x = g⁻¹ * z * θ g := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨h, rfl⟩ := h₂
  refine ⟨h * g, ?_⟩
  simp only [map_mul]
  group

theorem exists_over {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 K)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem finite_over {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) : {u : HeightOneSpectrum (𝓞 K) | u.under (𝓞 F) = v}.Finite := by
  have h := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
  refine (h.preimage (f := fun u : HeightOneSpectrum (𝓞 K) => u.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  intro u hu
  change u.under (𝓞 F) = v at hu
  refine ⟨u.isPrime, ⟨?_⟩⟩
  rw [← hu]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem thE_thE (n : ℕ) (g : GL (Fin n) E) : thE E n (thE E n g) = g :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun x => IsCMField.complexConj_apply_apply E x) g

theorem nrm_tw (n : ℕ) (z g : GL (Fin n) E) :
    (g⁻¹ * z * thE E n g) * thE E n (g⁻¹ * z * thE E n g) = g⁻¹ * (z * thE E n z) * g := by
  rw [map_mul, map_mul, map_inv, thE_thE]
  group

theorem locEl_tw (hU : Unr E) (n : ℕ) (w : Pl E) (z g : GL (Fin n) E) :
    ∃ h, locEl n w (g⁻¹ * z * thE E n g) = h⁻¹ * locEl n w z * thL n w h := by
  refine ⟨GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) g, ?_⟩
  unfold locEl thL
  split_ifs with hs
  · rw [nrm_tw, map_mul, map_mul, map_inv, MonoidHom.id_apply]
  · have hm : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n g) =
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) g) :=
      GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => (((_root_.GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1 x).symm) g
    rw [map_mul, map_mul, map_inv, hm]

theorem locEl_rel (hU : Unr E) (n : ℕ) (w : Pl E) {z z' : GL (Fin n) E} (h : ∃ g, z' = g⁻¹ * z * thE E n g)
    (yw : GLw n w) :
    (∃ g, locEl n w z = g⁻¹ * yw * thL n w g) ↔ ∃ g, locEl n w z' = g⁻¹ * yw * thL n w g := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨k, hk⟩ := locEl_tw hU n w z g
  rw [hk]
  constructor
  · intro hz
    exact tw_trans _ ⟨k, rfl⟩ hz
  · intro hz
    exact tw_trans _ (tw_symm _ ⟨k, rfl⟩) hz

theorem param_main (h1 : SkewEx) (h2 : Struct) (h3 : QuadField) (h4 : LocDict) (h5 : ClsNorm) (h6 : ClsOnto)
    (h7 : ClsEq) (h8 : LocGood) : Param := by
  intro E _ _ _ hU n S hS P hP y hy hyK
  obtain ⟨s, d, hs0, hsc, hsd⟩ := h1 E
  obtain ⟨δ, hδ⟩ := GlobalTheory.BCT.KapMul.exists_norm E hP
  have hPδ : (δ * thE E n δ).val.charpoly ∈ Ell E n := by rw [hδ]; exact hP
  have hsep : (δ * thE E n δ).val.charpoly.Separable := hPδ.2.2.1
  obtain ⟨ι, _, K, _, _, _, ρ, hcard, hreal, hsum, hfr⟩ := h2 E s d hs0 hsc hsd n δ hPδ
  choose hinf L fL nfL aL qL hLc hglob hloc using fun i => h3 E s d hs0 hsc hsd (K i) (hreal i)
  have hinv : ∀ x, (IsCMField.complexConj E).toRingEquiv.toRingHom
      ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = x := fun x => IsCMField.complexConj_apply_apply E x
  have hyδ : ∀ w, (nrmL n w (y w)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly := fun w => by
    rw [hδ]; exact hy w
  choose X hX using fun w => h4 E hU s d hs0 hsc hsd n δ hsep ι K ρ hfr w (y w) (hyδ w)
  have hW : ∀ i (u : HeightOneSpectrum (𝓞 (K i))), ∃ w ∈ S,
      w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) := by
    intro i u
    obtain ⟨w0, hw0⟩ := exists_over (K := E) (u.under (𝓞 (maximalRealSubfield E)))
    obtain ⟨w, ⟨hwS, hw⟩, -⟩ := hS w0
    exact ⟨w, hwS, hw.trans hw0⟩
  choose W hWS hWu using hW
  let x : ∀ i, GlobalTheory.QuadSymbol.FinFam (K i) := fun i u => X (W i u) i ⟨u, (hWu i u).symm⟩
  have hxX : ∀ i (w : Pl E) (u : {u : HeightOneSpectrum (𝓞 (K i)) //
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))}), w ∈ S → x i u.1 = X w i u := by
    intro i w u hw
    have e : W i u.1 = w := (hS w).unique ⟨hWS i u.1, (hWu i u.1).trans u.2⟩ ⟨hw, rfl⟩
    have key : ∀ (w1 : Pl E) (_ : w1 = w) (p : u.1.under (𝓞 (maximalRealSubfield E)) =
        w1.under (𝓞 (maximalRealSubfield E))), X w1 i ⟨u.1, p⟩ = X w i u := by
      rintro w1 rfl p; rfl
    exact key _ e _
  let ev : ∀ i, (∀ j, K j)ˣ →* (K i)ˣ := fun i => Units.map (Pi.evalMonoidHom K i)
  have hloc' : ∀ (t : (∀ i, K i)ˣ) (w : Pl E), w ∈ S →
      ((∃ g, locEl n w (pt δ ρ.toRingHom t) = g⁻¹ * y w * thL n w g) ↔
      ∀ i (u : {u : HeightOneSpectrum (𝓞 (K i)) //
        u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))}),
        x i u.1 / GlobalTheory.QuadSymbol.finDiag (K i) (ev i t) u.1 ∈
          GlobalTheory.QuadSymbol.normGroup (K i) (L i) (u.1.adicCompletion (K i))) := by
    intro t w hw
    rw [hX w t]
    refine forall_congr' fun i => forall_congr' fun u => ?_
    rw [hxX i w u hw, hloc i u.1]
    have hne : algebraMap (K i) (u.1.adicCompletion (K i)) ((t : ∀ j, K j) i) ≠ 0 :=
      (_root_.map_ne_zero _).2 (ev i t).ne_zero
    have hv : ((X w i u / GlobalTheory.QuadSymbol.finDiag (K i) (ev i t) u.1 : (u.1.adicCompletion (K i))ˣ) :
        u.1.adicCompletion (K i)) = (X w i u : u.1.adicCompletion (K i)) /
          algebraMap (K i) (u.1.adicCompletion (K i)) ((t : ∀ j, K j) i) := by
      rw [Units.val_div_eq_div_val]; rfl
    rw [hv]
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, by rw [h, mul_div_cancel_left₀ _ hne]⟩
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, by rw [div_eq_iff hne] at h; rw [h, mul_comm]⟩

  have hev : ∀ᶠ w : Pl E in cofinite, ∃ g, locEl n w (pt δ ρ.toRingHom 1) = g⁻¹ * y w * thL n w g := by
    filter_upwards [h8 E hU n P hP, hyK, FinFib.locEl_eventually_mem n δ] with w hw hyw hδw
    obtain ⟨g, hg⟩ := (hw (locEl n w δ) hδw (by rw [ThBasic.charpoly_nrmL hU, hδ])).2.2 (y w) hyw (hy w)
    refine ⟨g⁻¹, ?_⟩
    rw [hg, show pt δ ρ.toRingHom 1 = δ by simp [pt]]
    simp only [map_inv, inv_inv]
    group
  have hAN : ∀ i, GlobalTheory.QuadSymbol.AlmostNorm (K i) (L i) (x i) := by
    intro i
    have hbad := Filter.eventually_cofinite.1 hev
    refine (hbad.biUnion fun w _ =>
      finite_over (F := maximalRealSubfield E) (K := K i) (w.under (𝓞 (maximalRealSubfield E)))).subset ?_
    intro u hu
    have hWbad : W i u ∈ {w : Pl E | ¬ ∃ g, locEl n w (pt δ ρ.toRingHom 1) = g⁻¹ * y w * thL n w g} := by
      intro hgood
      apply hu
      have h0 := (hloc' 1 (W i u) (hWS i u)).1 hgood i ⟨u, (hWu i u).symm⟩
      have h1 : GlobalTheory.QuadSymbol.finDiag (K i) (ev i 1) u = 1 := by
        rw [map_one]
        exact map_one (GlobalTheory.QuadSymbol.toUnits (K i) (u.adicCompletion (K i)))
      rw [h1, div_one] at h0
      exact h0
    exact Set.mem_biUnion hWbad (hWu i u).symm
  have hC : ∀ c : {c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧
      ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g},
      ∃ (t : (∀ i, K i)ˣ) (g : GL (Fin n) E), c.1.rep = g⁻¹ * pt δ ρ.toRingHom t * thE E n g :=
    fun c => h6 E n _ hinv δ s hs0 hsc _ _ ρ.toRingHom hfr hsep c.1.rep (c.2.1.trans hδ.symm)
  choose tc gc htc using hC
  have hcond : ∀ c i u, x i u / GlobalTheory.QuadSymbol.finDiag (K i) (ev i (tc c)) u ∈
      GlobalTheory.QuadSymbol.normGroup (K i) (L i) (u.adicCompletion (K i)) := by
    intro c i u
    have hl : ∃ g, locEl n (W i u) (pt δ ρ.toRingHom (tc c)) = g⁻¹ * y (W i u) * thL n (W i u) g :=
      (locEl_rel hU n (W i u) ⟨gc c, htc c⟩ (y _)).2 (c.2.2 _ (hWS i u))
    exact (hloc' (tc c) (W i u) (hWS i u)).1 hl i ⟨u, (hWu i u).symm⟩
  refine ⟨ι, inferInstance, K, L, inferInstance, inferInstance, fL, nfL, aL, qL, x, ?_, hreal, hLc, hAN, ?_,
    ⟨Equiv.ofBijective (fun c i => ⟨QuotientGroup.mk (ev i (tc c)), ev i (tc c), rfl, hcond c i⟩) ⟨?_, ?_⟩⟩⟩
  · rw [hcard, hδ]
  · rw [Finset.sum_congr rfl (fun i _ => hinf i), ← Finset.sum_mul, hsum]
  · intro c c' hcc
    have hq : ∀ i, (ev i (tc c))⁻¹ * ev i (tc c') ∈ GlobalTheory.QuadSymbol.globalNorms (K i) (L i) := fun i =>
      QuotientGroup.eq.1 (congrArg (fun f => (f i).1) hcc)
    choose a b hab using fun i => (hglob i _).1 (hq i)
    have hrel : ∃ g, pt δ ρ.toRingHom (tc c) = g⁻¹ * pt δ ρ.toRingHom (tc c') * thE E n g := by
      refine (h7 E n _ hinv δ s hs0 hsc _ _ ρ.toRingHom hfr (tc c') (tc c)).2 ⟨a, b, funext fun i => ?_⟩
      have hi := hab i
      rw [Units.val_mul, Units.val_inv_eq_inv_val] at hi
      change (tc c' : ∀ j, K j) i = (tc c : ∀ j, K j) i * (a i ^ 2 - algebraMap (maximalRealSubfield E) (K i) d * b i ^ 2)
      rw [← hi]
      change (tc c' : ∀ j, K j) i = (tc c : ∀ j, K j) i * (((tc c : ∀ j, K j) i)⁻¹ * (tc c' : ∀ j, K j) i)
      rw [← mul_assoc, mul_inv_cancel₀ (show (tc c : ∀ j, K j) i ≠ 0 from (ev i (tc c)).ne_zero), one_mul]
    apply Subtype.ext
    rw [← FinFib.cls_rep _ c.1, ← FinFib.cls_rep _ c'.1, FinFib.cls_eq_iff]
    have e := FinFib.twR_equiv (thE E n)
    exact e.trans (e.symm ⟨gc c, htc c⟩) (e.trans (e.symm hrel) ⟨gc c', htc c'⟩)
  · intro f
    choose T hT hTc using fun i => (f i).2
    let Tu : (∀ i, K i)ˣ := ⟨fun i => (T i : K i), fun i => ((T i)⁻¹ : (K i)ˣ),
      funext fun i => (T i).mul_inv, funext fun i => (T i).inv_mul⟩
    have hTu : ∀ i, ev i Tu = T i := fun i => Units.ext rfl
    obtain ⟨g0, hg0⟩ : FinFib.twR (thE E n) (pt δ ρ.toRingHom Tu)
        (FinFib.cls (thE E n) (pt δ ρ.toRingHom Tu)).rep :=
      (FinFib.cls_eq_iff _ _ _).1 (FinFib.cls_rep _ _).symm
    have hmem : ((FinFib.cls (thE E n) (pt δ ρ.toRingHom Tu)).rep *
        thE E n (FinFib.cls (thE E n) (pt δ ρ.toRingHom Tu)).rep).val.charpoly = P ∧
        ∀ w ∈ S, ∃ g, locEl n w (FinFib.cls (thE E n) (pt δ ρ.toRingHom Tu)).rep = g⁻¹ * y w * thL n w g := by
      refine ⟨?_, fun w hw => ?_⟩
      · rw [hg0, nrm_tw, show pt δ ρ.toRingHom Tu * thE E n (pt δ ρ.toRingHom Tu) = δ * thE E n δ from
          h5 E n _ hinv δ s hs0 hsc _ _ ρ.toRingHom hfr Tu, ← hδ, Units.val_mul, Units.val_mul,
          Matrix.coe_units_inv, Matrix.charpoly_units_conj']
      · refine (locEl_rel hU n w ⟨g0, hg0⟩ (y w)).1 ((hloc' Tu w hw).2 fun i u => ?_)
        rw [hTu]
        exact hTc i u.1
    refine ⟨⟨FinFib.cls (thE E n) (pt δ ρ.toRingHom Tu), hmem⟩, funext fun i => Subtype.ext ?_⟩
    have hrel : ∃ g, pt δ ρ.toRingHom (tc ⟨_, hmem⟩) = g⁻¹ * pt δ ρ.toRingHom Tu * thE E n g := by
      have e := FinFib.twR_equiv (thE E n)
      exact e.trans ⟨g0, hg0⟩ (e.symm ⟨gc ⟨_, hmem⟩, htc ⟨_, hmem⟩⟩)
    obtain ⟨uu, vv, huv⟩ := (h7 E n _ hinv δ s hs0 hsc _ _ ρ.toRingHom hfr Tu (tc ⟨_, hmem⟩)).1 hrel
    change QuotientGroup.mk (ev i (tc ⟨_, hmem⟩)) = (f i).1
    rw [hT i, ← hTu i]
    refine QuotientGroup.eq.2 ((hglob i _).2 ⟨uu i, vv i, ?_⟩)
    have hi := congrFun huv i
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    change ((tc ⟨_, hmem⟩ : ∀ j, K j) i)⁻¹ * (Tu : ∀ j, K j) i = _
    rw [hi]
    change ((tc ⟨_, hmem⟩ : ∀ j, K j) i)⁻¹ * ((tc ⟨_, hmem⟩ : ∀ j, K j) i *
      (uu i ^ 2 - algebraMap (maximalRealSubfield E) (K i) d * vv i ^ 2)) = _
    rw [← mul_assoc, inv_mul_cancel₀ (show (tc ⟨_, hmem⟩ : ∀ j, K j) i ≠ 0 from (ev i (tc ⟨_, hmem⟩)).ne_zero), one_mul]

end PositivityTheory.Rg.BcB.G3.ParamP

namespace PositivityTheory.Rg.BcB.G3

theorem param_pf (h1 : SkewEx) (h2 : Struct) (h3 : QuadField) (h4 : LocDict) (h5 : ClsNorm) (h6 : ClsOnto)
    (h7 : ClsEq) (h8 : LocGood) : Param :=
  ParamP.param_main h1 h2 h3 h4 h5 h6 h7 h8

end PositivityTheory.Rg.BcB.G3

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TwistedTraceFormulaEllipticExpansion
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open GlobalTheory.BCT.FibStable PositivityTheory.Rg.BcB.G8
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

abbrev th2 (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w := (thL a w).prodMap (thL b w)

abbrev loc2 (w : Pl E) (x : GL (Fin a) E) (y : GL (Fin b) E) : GLw a w × GLw b w := (locEl a w x, locEl b w y)

def orb2 (S : Set (Pl E)) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (c : TwCl (thE E a) × TwCl (thE E b)) : ℂ :=
  ∏ᶠ w ∈ S, twOrb (th2 a b w) (K2 a b w) (loc2 w c.1.rep c.2.rep) (φ w)

theorem local_pair_mem_maximal_eventually (x : GL (Fin a) E) (y : GL (Fin b) E) : ∀ᶠ w : Pl E in cofinite, loc2 w x y ∈ K2 a b w := by
  filter_upwards [GoodInt.eventually_mem_KGL x, GoodInt.eventually_mem_KGL (x * thE E a x),
    GoodInt.eventually_mem_KGL y, GoodInt.eventually_mem_KGL (y * thE E b y)] with w h1 h2 h3 h4
  refine ⟨?_, ?_⟩
  · show locEl a w x ∈ _
    unfold locEl
    split_ifs
    exacts [h2, h1]
  · show locEl b w y ∈ _
    unfold locEl
    split_ifs
    exacts [h4, h3]

theorem charpoly_conj2 (w : Pl E) (g y : GLw a w × GLw b w) :
    (nrmL a w (g⁻¹ * y * th2 a b w g).1).val.charpoly = (nrmL a w y.1).val.charpoly ∧
      (nrmL b w (g⁻¹ * y * th2 a b w g).2).val.charpoly = (nrmL b w y.2).val.charpoly :=
  ⟨charpoly_twConj a w g.1 y.1, charpoly_twConj b w g.2 y.2⟩

theorem pairSum (hA : AbsSum) (hF : FinCl2) (hI : Invar2) (hN : Unit2) (hC : Count2) (hU : Unr E) (S : Set (Pl E))
    (hS : IsSection S) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (hφ : IsTestP φ) (P₁ P₂ : E[X]) (h₁ : P₁ ∈ Ell E a)
    (h₂ : P₂ ∈ Ell E b) :
    {c | (pol c.1 = P₁ ∧ pol c.2 = P₂) ∧ orb2 S φ c ≠ 0}.Finite ∧
      (∑ᶠ c, if pol c.1 = P₁ ∧ pol c.2 = P₂ then orb2 S φ c else 0) * 2 ^ (nfac P₁ + nfac P₂) =
        2 ^ ((a + b) * Fintype.card (InfinitePlace E)) * ∏ᶠ w ∈ S, stTw2 a b w (atPl w P₁) (atPl w P₂) (φ w) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hφ⟩ := hφ
  obtain ⟨δ₁, hδ₁⟩ := KapMul.exists_norm E h₁
  obtain ⟨δ₂, hδ₂⟩ := KapMul.exists_norm E h₂
  have hinv : ∀ w y, twOrb (th2 a b w) (K2 a b w) (cls (th2 a b w) y).rep (φ w) = twOrb (th2 a b w) (K2 a b w) y (φ w) := by
    intro w y
    obtain ⟨g, hg⟩ := rep_cls (th2 a b w) y
    rw [hg]
    exact hI E hU a b w _ _ (hK₁.1 w) (hK₂.1 w) _ (hφ.1 w) y g
  have hpol : ∀ (w : Pl E) (y : GLw a w × GLw b w), (nrmL a w (cls (th2 a b w) y).rep.1).val.charpoly = (nrmL a w y.1).val.charpoly ∧
      (nrmL b w (cls (th2 a b w) y).rep.2).val.charpoly = (nrmL b w y.2).val.charpoly := by
    intro w y
    obtain ⟨g, hg⟩ := rep_cls (th2 a b w) y
    rw [hg]
    exact charpoly_conj2 w g y
  have hl : ∀ (w : Pl E) (x : GL (Fin a) E) (y : GL (Fin b) E), (x * thE E a x).val.charpoly = P₁ → (y * thE E b y).val.charpoly = P₂ →
      (nrmL a w (loc2 w x y).1).val.charpoly = atPl w P₁ ∧ (nrmL b w (loc2 w x y).2).val.charpoly = atPl w P₂ :=
    fun w x y hx hy => ⟨by rw [← hx]; exact ThBasic.charpoly_nrmL hU a w x, by rw [← hy]; exact ThBasic.charpoly_nrmL hU b w y⟩
  have key := hA (Pl E) (TwCl (thE E a) × TwCl (thE E b)) S (fun w => TwCl (th2 a b w))
    (fun w => {l | (nrmL a w l.rep.1).val.charpoly = atPl w P₁ ∧ (nrmL b w l.rep.2).val.charpoly = atPl w P₂})
    (fun w => cls _ (loc2 w δ₁ δ₂)) (fun w l => twOrb (th2 a b w) (K2 a b w) l.rep (φ w))
    {c | pol c.1 = P₁ ∧ pol c.2 = P₂} (fun c w => cls _ (loc2 w c.1.rep c.2.rep)) (2 ^ (nfac P₁ + nfac P₂))
    (2 ^ ((a + b) * Fintype.card (InfinitePlace E)))
    (fun w => hF E hU a b w _ _ h₁.2.2.1.map h₂.2.2.1.map)
    (fun w => ⟨(hpol w _).1.trans (hl w _ _ hδ₁ hδ₂).1, (hpol w _).2.trans (hl w _ _ hδ₁ hδ₂).2⟩)
    (by
      filter_upwards [hN E hU a b P₁ h₁ P₂ h₂, hφ.2, local_pair_mem_maximal_eventually δ₁ δ₂] with w h1 h2 h3 l hl'
      rw [h2, (h1 l.rep _ hl'.1 hl'.2 (hl w _ _ hδ₁ hδ₂).1 (hl w _ _ hδ₁ hδ₂).2 h3).1]
      refine if_congr ?_ rfl rfl
      rw [← cls_eq_iff, cls_rep, eq_comm])
    (fun c hc => ⟨fun w => ⟨(hpol w _).1.trans (hl w _ _ hc.1 hc.2).1, (hpol w _).2.trans (hl w _ _ hc.1 hc.2).2⟩, by
      filter_upwards [hN E hU a b P₁ h₁ P₂ h₂, local_pair_mem_maximal_eventually c.1.rep c.2.rep, local_pair_mem_maximal_eventually δ₁ δ₂] with w h1 h2 h3
      exact ((cls_eq_iff _ _ _).2 ((h1 _ _ (hl w _ _ hc.1 hc.2).1 (hl w _ _ hc.1 hc.2).2 (hl w _ _ hδ₁ hδ₂).1
        (hl w _ _ hδ₁ hδ₂).2 h3).2 h2)).symm⟩)
    (pow_ne_zero _ two_ne_zero)
    (fun y hy hy' => hC E hU a b S hS P₁ h₁ P₂ h₂ y hy (by
      filter_upwards [hy', local_pair_mem_maximal_eventually δ₁ δ₂] with w h1 h2
      exact ⟨_, h2, h1⟩))
  simp only [hinv, Set.mem_setOf_eq, Nat.cast_pow, Nat.cast_ofNat] at key
  refine ⟨key.1, key.2.trans ?_⟩
  congr 1
  refine finprod_mem_congr rfl fun w _ => ?_
  unfold stTw2 clSum
  refine finsum_congr fun d => ?_
  simp only [Set.mem_setOf_eq, Pi.one_apply, one_mul]

theorem orbit_pair_nonzero_local (hN : Unit2) (hZ : Supp) (hU : Unr E) (S : Set (Pl E)) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ)
    (hφ : IsTestP φ) (c : TwCl (thE E a) × TwCl (thE E b)) (h₁ : pol c.1 ∈ Ell E a) (h₂ : pol c.2 ∈ Ell E b)
    (h : orb2 S φ c ≠ 0) : ∀ w ∈ S, ∃ y : GLw a w × GLw b w, φ w y ≠ 0 ∧
      (nrmL a w y.1).val.charpoly = atPl w (pol c.1) ∧ (nrmL b w y.2).val.charpoly = atPl w (pol c.2) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hφ⟩ := hφ
  intro w hw
  have hl : ∀ w : Pl E, (nrmL a w (loc2 w c.1.rep c.2.rep).1).val.charpoly = atPl w (pol c.1) ∧
      (nrmL b w (loc2 w c.1.rep c.2.rep).2).val.charpoly = atPl w (pol c.2) :=
    fun w => ⟨ThBasic.charpoly_nrmL hU a w _, ThBasic.charpoly_nrmL hU b w _⟩
  have hfin : ∀ᶠ w in cofinite, twOrb (th2 a b w) (K2 a b w) (loc2 w c.1.rep c.2.rep) (φ w) = 1 := by
    filter_upwards [hN E hU a b _ h₁ _ h₂, hφ.2, local_pair_mem_maximal_eventually c.1.rep c.2.rep] with w h1 h2 h3
    rw [h2, (h1 _ _ (hl w).1 (hl w).2 (hl w).1 (hl w).2 h3).1, if_pos ⟨1, by rw [map_one, inv_one, one_mul, mul_one]⟩]
  have hne : twOrb (th2 a b w) (K2 a b w) (loc2 w c.1.rep c.2.rep) (φ w) ≠ 0 := by
    intro h0
    apply h
    unfold orb2
    have hf : (S ∩ Function.mulSupport fun w => twOrb (th2 a b w) (K2 a b w) (loc2 w c.1.rep c.2.rep) (φ w)).Finite :=
      (Filter.eventually_cofinite.1 hfin).subset fun w hw => hw.2
    rw [finprod_mem_eq_prod _ hf]
    exact Finset.prod_eq_zero (i := w) (by simp [hw, h0]) h0
  obtain ⟨g, hg⟩ := hZ _ _ _ _ _ hne
  exact ⟨_, hg, (charpoly_conj2 w g _).1.trans (hl w).1, (charpoly_conj2 w g _).2.trans (hl w).2⟩

theorem twisted_trace_formula_elliptic_expansion (hA : AbsSum) (hF : FinCl2) (hI : Invar2) (hN : Unit2) (hC : Count2) (hZ : Supp) (hP : FinPol2) :
    G8.G3 := by
  intro E _ _ _ hU a b S hS l₁ l₂ φ hφ hreg
  have hsum := pairSum hA hF hI hN hC hU S hS φ hφ
  have hne := orbit_pair_nonzero_local hN hZ hU S φ hφ
  have hQ := (let ⟨_, _, _, _, h⟩ := hφ; hP E hU a b S hS φ (fun w => (h.1 w).1) h.2)
  set Q₀ := {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ ∀ w ∈ S, ∃ y : GLw a w × GLw b w, φ w y ≠ 0 ∧
    (nrmL a w y.1).val.charpoly = atPl w p.1 ∧ (nrmL b w y.2).val.charpoly = atPl w p.2} with hQ₀
  have hcop : ∀ p ∈ Q₀, IsCoprime p.1 p.2 := by
    rintro p ⟨-, -, hp⟩
    obtain ⟨w, hw, hr⟩ := hreg
    obtain ⟨y, hy, e1, e2⟩ := hp w hw
    have := hr y hy
    rw [e1, e2, ← Polynomial.map_mul, Polynomial.separable_map] at this
    exact this.isCoprime
  set pc : TwCl (thE E a) × TwCl (thE E b) → E[X] × E[X] := fun c => (pol c.1, pol c.2) with hpc
  have hB : {c | (pol c.1 ∈ Ell E a ∧ pol c.2 ∈ Ell E b) ∧ orb2 S φ c ≠ 0}.Finite := by
    refine (hQ.biUnion fun p hp => (hsum p.1 p.2 hp.1 hp.2.1).1).subset ?_
    rintro c ⟨h1, h2⟩
    exact Set.mem_biUnion (x := pc c) ⟨h1.1, h1.2, hne c h1.1 h1.2 h2⟩ ⟨⟨rfl, rfl⟩, h2⟩
  have hmaps : ∀ c ∈ hB.toFinset, pc c ∈ hQ.toFinset := by
    intro c hc
    rw [Set.Finite.mem_toFinset] at hc ⊢
    exact ⟨hc.1.1, hc.1.2, hne c hc.1.1 hc.1.2 hc.2⟩
  have e1 : geomRat2 S l₁ l₂ φ = ∑ c ∈ hB.toFinset, kap (pol c.1) * kap (pol c.2) * chW l₁ (pol c.1) * chW l₂ (pol c.2) *
      (orb2 S φ c * 2 ^ (nfac (pol c.1) + nfac (pol c.2))) := by
    unfold geomRat2
    rw [finsum_eq_sum_of_support_subset (s := hB.toFinset)]
    · refine Finset.sum_congr rfl fun c hc => ?_
      rw [Set.Finite.mem_toFinset] at hc
      rw [if_pos hc.1, MassP.mass_kap E hU a c.1.rep hc.1.1, MassP.mass_kap E hU b c.2.rep hc.1.2, pow_add]
      unfold orb2 pol
      ring
    · intro c hc
      rw [Function.mem_support] at hc
      rw [Set.Finite.coe_toFinset]
      split_ifs at hc with h
      · exact ⟨h, right_ne_zero_of_mul hc⟩
      · exact absurd rfl hc
  have e3 : ∀ p : E[X] × E[X], p.1 ∈ Ell E a → p.2 ∈ Ell E b →
      (∑ᶠ c, if pol c.1 = p.1 ∧ pol c.2 = p.2 then orb2 S φ c else 0) = ∑ c ∈ hB.toFinset with pc c = p, orb2 S φ c := by
    intro p p1 p2
    rw [finsum_eq_sum_of_support_subset (s := hB.toFinset), Finset.sum_filter]
    · exact Finset.sum_congr rfl fun c _ => if_congr (Prod.ext_iff (x := pc c) (y := p)).symm rfl rfl
    · intro c hc
      rw [Function.mem_support] at hc
      rw [Set.Finite.coe_toFinset]
      split_ifs at hc with h
      · exact ⟨⟨h.1 ▸ p1, h.2 ▸ p2⟩, hc⟩
      · exact absurd rfl hc
  have e2 : G8.geomSt2 S l₁ l₂ φ = ∑ p ∈ hQ.toFinset, kap p.1 * kap p.2 * chW l₁ p.1 * chW l₂ p.2 *
      ∏ᶠ w ∈ S, stTw2 a b w (atPl w p.1) (atPl w p.2) (φ w) := by
    unfold G8.geomSt2
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext p
    simp only [Set.mem_inter_iff, Function.mem_support, Set.Finite.coe_toFinset]
    refine and_congr_left fun h => ⟨fun hp => ?_, fun hp => ⟨hp.1, hp.2.1, hcop p hp⟩⟩
    have h2 := (hsum p.1 p.2 hp.1 hp.2.1).2
    rw [e3 p hp.1 hp.2.1] at h2
    have h3 : ∑ c ∈ hB.toFinset with pc c = p, orb2 S φ c ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at h2
      exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (right_ne_zero_of_mul h) h2.symm
    obtain ⟨c, hc, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h3
    rw [Finset.mem_filter] at hc
    have := hmaps c hc.1
    rwa [hc.2, Set.Finite.mem_toFinset] at this
  rw [e1, e2, Finset.mul_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Set.Finite.mem_toFinset] at hp
  have h2 := (hsum p.1 p.2 hp.1 hp.2.1).2
  rw [e3 p hp.1 hp.2.1] at h2
  calc _ = kap p.1 * kap p.2 * chW l₁ p.1 * chW l₂ p.2 *
        ((∑ c ∈ hB.toFinset with pc c = p, orb2 S φ c) * 2 ^ (nfac p.1 + nfac p.2)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [← (Finset.mem_filter.1 hc).2]
    _ = _ := by rw [h2]; ring

end PositivityTheory.Rg.BcB.G3

end
end

