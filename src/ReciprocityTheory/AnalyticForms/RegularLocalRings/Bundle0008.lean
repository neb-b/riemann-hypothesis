module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.AtlasA
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}

theorem analyticAt_eval_of_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {σ : Type*}
    {f : E → σ → ℂ} {z : E} (hf : ∀ l, AnalyticAt ℂ (f · l) z) (p : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun x => eval (f x) p) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact analyticAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p l hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (hf l)

def AlgRes.GoodChart (R : AlgRes (ι := ι) P D e) (ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)) : Prop :=
  ∃ i, ψ.source ⊆ R.src i ∧
    (∃ r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ, ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y)) ∧
    ∃ g : (Fin e → ℂ) → Fin (R.amb i) → ℂ, AnalyticOnNhd ℂ g ψ.target ∧
      ∀ w ∈ ψ.target, R.coord i (ψ.symm w) = g w

theorem AlgRes.analyticAt_coord_symm (R : AlgRes (ι := ι) P D e)
    {ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)} {i : Fin R.n} (hs : ψ.source ⊆ R.src i)
    {g : (Fin e → ℂ) → Fin (R.amb i) → ℂ} (hg : AnalyticOnNhd ℂ g ψ.target)
    (hgc : ∀ w ∈ ψ.target, R.coord i (ψ.symm w) = g w)
    (j : Fin R.n) (h : MvPolynomial (Fin (R.amb j)) ℂ) {w : Fin e → ℂ} (hw : w ∈ ψ.target)
    (hwj : ψ.symm w ∈ R.src j) :
    AnalyticAt ℂ (fun w => eval (R.coord j (ψ.symm w)) h) w := by
  have hwS : ψ.symm w ∈ ψ.source := ψ.map_target hw
  have hxi : ψ.symm w ∈ R.src i := hs hwS
  obtain ⟨q, F, hq0, hqF⟩ := R.trans i j (ψ.symm w) ⟨hxi, hwj⟩
  have hgw : AnalyticAt ℂ g w := hg w hw
  have hga : ∀ l, AnalyticAt ℂ (g · l) w := fun l =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (R.amb i) => ℂ) l).analyticAt (g w)).comp hgw
  have hFa : ∀ l, AnalyticAt ℂ (fun w' => eval (g w') (F l)) w := fun l =>
    analyticAt_eval_of_pi hga (F l)
  have hqa : AnalyticAt ℂ (fun w' => eval (g w') q) w := analyticAt_eval_of_pi hga q
  have hq0' : eval (g w) q ≠ 0 := by
    rw [← hgc w hw]
    exact hq0
  have hA : AnalyticAt ℂ (fun w' => eval (fun l => eval (g w') (F l) / eval (g w') q) h) w :=
    analyticAt_eval_of_pi (f := fun w' l => eval (g w') (F l) / eval (g w') q)
      (fun l => (hFa l).div hqa hq0') h
  refine hA.congr ?_
  have ht : ψ.target ∈ 𝓝 w := ψ.open_target.mem_nhds hw
  have hj : ∀ᶠ w' in 𝓝 w, ψ.symm w' ∈ R.src j :=
    (ψ.continuousAt_symm hw).preimage_mem_nhds ((R.isOpen_alt_bis j).mem_nhds hwj)
  have hqne : ∀ᶠ w' in 𝓝 w, eval (g w') q ≠ 0 := hqa.continuousAt.eventually_ne hq0'
  filter_upwards [ht, hj, hqne] with w' h1 h2 h3
  have hsrc : ψ.symm w' ∈ R.src i := hs (ψ.map_target h1)
  have hcw : R.coord i (ψ.symm w') = g w' := hgc w' h1
  have hfun : (fun l => eval (g w') (F l) / eval (g w') q) = R.coord j (ψ.symm w') := by
    funext l
    have hl := hqF (ψ.symm w') ⟨hsrc, h2⟩ (by rw [hcw]; exact h3) l
    rw [hcw] at hl
    rw [div_eq_iff h3]
    exact hl.symm
  exact congrArg (fun v => eval v h) hfun

theorem AlgRes.analyticOnNhd_comp_symm (R : AlgRes (ι := ι) P D e)
    {ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)} (hψ : R.GoodChart ψ) {m : ℕ}
    (f : R.M → Fin m → ℂ) (S : Set R.M) (hS : IsOpen S) (j : Fin R.n) (hSj : S ⊆ R.src j)
    (r : Fin m → MvPolynomial (Fin (R.amb j)) ℂ) (hf : ∀ y ∈ S, f y = evalFam r (R.coord j y)) :
    AnalyticOnNhd ℂ (f ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' S) := by
  obtain ⟨i, hsi, -, g, hg, hgc⟩ := hψ
  rintro w ⟨hw, hwS⟩
  have hwS' : ψ.symm w ∈ S := hwS
  have hev : (fun w' => evalFam r (R.coord j (ψ.symm w'))) =ᶠ[𝓝 w] (f ∘ ψ.symm) := by
    have hS' : ∀ᶠ w' in 𝓝 w, ψ.symm w' ∈ S :=
      (ψ.continuousAt_symm hw).preimage_mem_nhds (hS.mem_nhds hwS')
    filter_upwards [hS'] with w' h1
    exact (hf _ h1).symm
  refine AnalyticAt.congr ?_ hev
  rw [analyticAt_pi_iff]
  intro l
  exact R.analyticAt_coord_symm hsi hg hgc j (r l) hw (hSj hwS')

theorem AlgRes.exists_goodChart (R : AlgRes (ι := ι) P D e) (i : Fin R.n) (x : R.M) (hx : x ∈ R.src i)
    (r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ)
    (hr : Ideal.span (Set.range fun l => algebraMap _ (locRing (R.ideal i) (R.coord i x)) (r l)) =
      Ideal.map (algebraMap _ (locRing (R.ideal i) (R.coord i x))) (ptIdeal (R.coord i x)))
    (O : Set R.M) (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ), R.GoodChart ψ ∧ x ∈ ψ.source ∧
      ψ.source ⊆ O ∩ R.src i ∧ ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y) := by
  have := R.regular i x hx
  obtain ⟨U, V, g, hU, hpU, hV, hg, hbij, hrg⟩ :=
    exists_holo_coords (R.ideal i) (R.coord i x) e (R.dim i x hx) r hr
  have hcont : ContinuousOn (R.coord i) (R.src i) := by
    rw [continuousOn_iff_continuous_domRestrict]; exact (R.isEmbedding i).continuous
  have hinj : Set.InjOn (R.coord i) (R.src i) := fun a ha b hb hab =>
    congrArg Subtype.val ((R.isEmbedding i).injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  have hev : Continuous (evalFam r) := continuous_pi fun l => MvPolynomial.continuous_eval (p := r l)
  have hzero : ∀ y ∈ R.src i, R.coord i y ∈ zeroSet (R.ideal i) := by
    intro y hy
    have : R.coord i y ∈ R.coord i '' R.src i := ⟨y, hy, rfl⟩
    rw [R.image i] at this
    exact this
  have hex : ∀ w ∈ V, ∃ y ∈ R.src i, R.coord i y = g w := by
    intro w hw
    have h1 : g w ∈ zeroSet (R.ideal i) := (hbij.mapsTo hw).2
    have hmem : g w ∈ R.coord i '' R.src i := by rw [R.image i]; exact h1
    obtain ⟨y, hy, hyw⟩ := hmem
    exact ⟨y, hy, hyw⟩
  classical
  let inv : (Fin e → ℂ) → R.M := fun w =>
    if h : ∃ y ∈ R.src i, R.coord i y = g w then h.choose else x
  have hinv : ∀ w ∈ V, inv w ∈ R.src i ∧ R.coord i (inv w) = g w := by
    intro w hw
    have h := hex w hw
    simp only [inv, dif_pos h]
    exact h.choose_spec
  have hback : ∀ y ∈ R.src i, R.coord i y ∈ U → g (evalFam r (R.coord i y)) = R.coord i y := by
    intro y hy hyU
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hyU, hzero y hy⟩
    rw [← hgw, hrg w hw]
  let S : Set R.M := R.src i ∩ R.coord i ⁻¹' (U ∩ evalFam r ⁻¹' V)
  have hSo : IsOpen S := hcont.isOpen_inter_preimage (R.isOpen_alt_bis i) (hU.inter (hV.preimage hev))
  have hmapT : ∀ w ∈ V, inv w ∈ S := by
    intro w hw
    obtain ⟨h1, h2⟩ := hinv w hw
    refine ⟨h1, ?_⟩
    show R.coord i (inv w) ∈ U ∩ evalFam r ⁻¹' V
    rw [h2]
    refine ⟨(hbij.mapsTo hw).1, ?_⟩
    show evalFam r (g w) ∈ V
    rw [hrg w hw]
    exact hw
  have hcinv : ContinuousOn inv V := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : V → R.src i := fun w => ⟨inv w, (hinv w w.2).1⟩
    have hf : Continuous f := by
      rw [(R.isEmbedding i).continuous_iff]
      have : ((fun y : R.src i => R.coord i y) ∘ f) = fun w : V => g w :=
        funext fun w => (hinv w w.2).2
      rw [this]
      exact hg.continuousOn.domRestrict
    exact continuous_subtype_val.comp hf
  let ψ0 : OpenPartialHomeomorph R.M (Fin e → ℂ) :=
    { toFun := fun y => evalFam r (R.coord i y)
      invFun := inv
      source := S
      target := V
      map_source' := fun y hy => hy.2.2
      map_target' := fun w hw => hmapT w hw
      left_inv' := fun y hy => by
        obtain ⟨h1, h2⟩ := hinv _ hy.2.2
        exact hinj h1 hy.1 (h2.trans (hback y hy.1 hy.2.1))
      right_inv' := fun w hw => by
        obtain ⟨-, h2⟩ := hinv w hw
        show evalFam r (R.coord i (inv w)) = w
        rw [h2, hrg w hw]
      open_source := hSo
      open_target := hV
      continuousOn_toFun := (hev.comp_continuousOn hcont).mono fun y hy => hy.1
      continuousOn_invFun := hcinv }
  have hxS : x ∈ S := by
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hpU, hzero x hx⟩
    refine ⟨hx, hpU, ?_⟩
    show evalFam r (R.coord i x) ∈ V
    rw [← hgw, hrg w hw]
    exact hw
  refine ⟨ψ0.restrOpen O hO, ⟨i, fun y hy => hy.1.1, ⟨r, fun y _ => rfl⟩, g,
    hg.mono fun w hw => hw.1, fun w hw => (hinv w hw.1).2⟩, ⟨hxS, hxO⟩,
    fun y hy => ⟨hy.2, hy.1.1⟩, fun y _ => rfl⟩

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.MemBasicOpenSecHomIff
section
open AlgebraicGeometry CategoryTheory MvPolynomial

namespace ReciprocityTheory.AnForm.R

noncomputable section

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

namespace AffPres

variable (P : AffPres s)

theorem mem_basicOpen_secHom_iff (x : W) (hx : x ∈ P.V) (f : MvPolynomial (Fin P.n) ℂ) :
    x ∈ W.basicOpen (P.secHom f) ↔ f ∉ P.ptOf x hx := by
  set g := (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv
    (Ideal.Quotient.mk P.K f) with hg
  have h1 : x ∈ W.basicOpen (P.secHom f) ↔
      (⟨x, hx⟩ : P.V.toScheme) ∈ P.V.toScheme.basicOpen (P.iso.hom.app ⊤ g) := by
    rw [Scheme.Opens.mem_basicOpen_toScheme]
    have e : P.secHom f = W.presheaf.map (eqToHom P.V.ι_image_top.symm).op (P.iso.hom.app ⊤ g) := rfl
    have e' := Scheme.basicOpen_res W (i := (eqToHom P.V.ι_image_top.symm).op)
      (f := (P.iso.hom.app ⊤ g : Γ(W, P.V.ι ''ᵁ ⊤)))
    rw [e]
    refine (Iff.of_eq (congrArg (fun O => x ∈ O) e')).trans ?_
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have e2 := Scheme.preimage_basicOpen P.iso.hom g
  refine h1.trans (Iff.trans (Iff.of_eq (congrArg (fun O => (⟨x, hx⟩ : P.V.toScheme) ∈ O) e2.symm)) ?_)
  show P.iso.hom.base ⟨x, hx⟩ ∈ (Spec _).basicOpen g ↔ _
  have e4 := AlgebraicGeometry.basicOpen_eq_of_affine
    (R := .of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)) (Ideal.Quotient.mk P.K f)
  rw [hg, e4]
  exact Iff.rfl

theorem secHom_C' (c : ℂ) : P.secHom (C c) = constSec s P.V c := by
  have e1 : P.secHom (C c) = P.V.topIso.hom (P.iso.hom.appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv (Ideal.Quotient.mk P.K (C c)))) := rfl
  have e2 : (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv (Ideal.Quotient.mk P.K (C c)) =
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop
        ((Scheme.ΓSpecIso (.of ℂ)).inv c) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have e3 : P.iso.hom.appTop ((Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) =
      (P.V.ι ≫ s).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c) := by
    rw [← P.hover]
    rfl
  have key : (Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appTop ≫
      W.presheaf.map (homOfLE (le_top : P.V.ι ''ᵁ ⊤ ≤ ⊤)).op ≫
        W.presheaf.map (eqToHom P.V.ι_image_top.symm).op =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appLE ⊤ P.V le_top := by
    rw [← Functor.map_comp]
    rfl
  rw [e1, e2, e3]
  exact congrArg (fun φ => φ.hom c) key

theorem eval_coord_eq_val [LocallyOfFiniteType s] (x : W) (hx : x ∈ P.V)
    (hc : IsClosed ({x} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    eval (P.coord x hx) f = val s (P.secHom f) x hx := by
  obtain ⟨φ, hφ⟩ := val_ringHom s P.V x hx hc
  set ψ := φ.comp P.secHom with hψdef
  have hC : ∀ c, ψ (C c) = c := by
    intro c
    rw [hψdef, RingHom.comp_apply, hφ, secHom_C', val_const s _ x hx hc]
  have hker : ∀ g, ψ g = 0 → g ∈ P.ptOf x hx := by
    intro g h
    by_contra hg
    rw [← mem_basicOpen_secHom_iff] at hg
    rw [hψdef, RingHom.comp_apply, hφ, val_eq_zero_iff s _ x hx hc,
      Scheme.evaluation_eq_zero_iff_notMem_basicOpen] at h
    exact h hg
  have hpr : P.ptOf x hx ≠ ⊤ :=
    Ideal.comap_ne_top _ (P.iso.hom.base ⟨x, hx⟩).isPrime.ne_top
  have hX : ∀ j, ψ (X j) = P.coord x hx j := by
    intro j
    have h1 : X j - C (ψ (X j)) ∈ P.ptOf x hx := hker _ (by rw [map_sub, hC, sub_self])
    have h2 : X j - C (P.coord x hx j) ∈ P.ptOf x hx :=
      Classical.epsilon_spec (p := fun c : ℂ => X j - C c ∈ P.ptOf x hx) ⟨_, h1⟩
    have h3 : C (ψ (X j) - P.coord x hx j) ∈ P.ptOf x hx := by
      have := sub_mem h2 h1
      rwa [sub_sub_sub_cancel_left, ← map_sub] at this
    by_contra hne
    have hu : IsUnit (C (ψ (X j) - P.coord x hx j) : MvPolynomial (Fin P.n) ℂ) :=
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)).map C
    exact hpr (Ideal.eq_top_of_isUnit_mem _ h3 hu)
  have hψ : ψ = eval (P.coord x hx) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [hC, eval_C]
    · intro j; rw [hX, eval_X]
  rw [← hφ]
  exact (RingHom.congr_fun hψ f).symm

end AffPres

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.SecHomSurjective
section
namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}

theorem val_eval₂ {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType s] {U : S.Opens}
    {σ : Type} (u : σ → Γ(S, U)) (F : MvPolynomial σ ℂ) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) :
    val s (eval₂ (constSec s U) u F) x hx = eval (fun t => val s (u t) x hx) F := by
  obtain ⟨φ, hφ⟩ := val_ringHom s U x hx hc
  rw [← hφ, eval₂_comp_left]
  have h1 : φ.comp (constSec s U) = RingHom.id ℂ := by
    ext c
    simp only [RingHom.comp_apply, hφ, RingHom.id_apply]
    exact val_const s U x hx hc c
  rw [h1]
  change eval₂ (RingHom.id ℂ) (φ ∘ u) F = eval₂ (RingHom.id ℂ) _ F
  congr 1
  funext t
  exact hφ (u t)

namespace AffPres


set_option backward.isDefEq.respectTransparency false in
theorem secHom_C (P : AffPres sW) (c : ℂ) : P.secHom (C c) = constSec sW P.V c := by
  have key : (Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sW.appLE ⊤ P.V le_top := by
    rw [← Scheme.Hom.comp_appTop_assoc, P.hover, Scheme.Hom.comp_appTop, Category.assoc]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Opens.ι_appTop,
      Scheme.Opens.topIso_hom, ← W.presheaf.map_comp]
    rfl
  have e3 : P.secHom (C c) = ((CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K))) ≫
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom) c := rfl
  rw [e3, Scheme.ΓSpecIso_inv_naturality_assoc, key]
  rfl

theorem secHom_surjective (P : AffPres sW) : Function.Surjective P.secHom := by
  intro a
  have h1 : Function.Surjective P.V.topIso.hom.hom :=
    (ConcreteCategory.bijective_of_isIso P.V.topIso.hom).2
  have h2 : Function.Surjective (P.iso.hom.app ⊤).hom :=
    (ConcreteCategory.bijective_of_isIso (P.iso.hom.app ⊤)).2
  have h3 : Function.Surjective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2
  obtain ⟨a1, rfl⟩ := h1 a
  obtain ⟨a2, rfl⟩ := h2 a1
  obtain ⟨a3, rfl⟩ := h3 a2
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a3
  exact ⟨f, rfl⟩

theorem val_secHom [LocallyOfFiniteType sW] (P : AffPres sW) (y : W) (hy : y ∈ P.V)
    (hc : IsClosed ({y} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    val sW (P.secHom f) y hy = eval (P.coord y hy) f := by
  obtain ⟨φ, hφ⟩ := val_ringHom sW P.V y hy hc
  have hker : ∀ g ∈ ptIdeal (P.coord y hy), val sW (P.secHom g) y hy = 0 := by
    intro g hg
    rw [val_eq_zero_iff sW _ y hy hc, ← Scheme.germ_residue, CommRingCat.comp_apply]
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    have h2 : P.stalkEquiv y hy hc (W.presheaf.germ P.V y hy (P.secHom g)) ∈
        (IsLocalRing.maximalIdeal (W.presheaf.stalk y)).map (P.stalkEquiv y hy hc) := by
      rw [P.map_maximalIdeal_stalk y hy hc, P.stalkEquiv_germ]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨w, hw, hwe⟩ := (Ideal.mem_map_of_equiv _ _).mp h2
    rw [(P.stalkEquiv y hy hc).injective hwe] at hw
    exact hw
  let ψ : MvPolynomial (Fin P.n) ℂ →+* ℂ := φ.comp P.secHom
  have hψ : ∀ g, ψ g = val sW (P.secHom g) y hy := fun g => hφ _
  have hC : ∀ c, ψ (C c) = c := fun c => by
    rw [hψ, secHom_C, val_const sW P.V y hy hc]
  have hX : ∀ j, ψ (MvPolynomial.X j) = P.coord y hy j := fun j => by
    have hm : X j - C (P.coord y hy j) ∈ ptIdeal (P.coord y hy) := by
      simp [ptIdeal, RingHom.mem_ker]
    have := hker _ hm
    rw [← hψ, map_sub, hC, sub_eq_zero] at this
    exact this
  have hext : ψ = MvPolynomial.eval (P.coord y hy) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [hC, eval_C]
    · intro j; rw [hX, eval_X]
  rw [← hψ, hext]

end AffPres

theorem exists_ratio_core {S T : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (t : T ⟶ Spec (.of ℂ))
    (g : S ⟶ T) (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t]
    (V : T.Opens) (hV : IsAffineOpen V) {σ : Type} (u : σ → Γ(T, V))
    (hu : ∀ a : Γ(T, V), ∃ F : MvPolynomial σ ℂ, a = eval₂ (constSec t V) u F)
    {ι : Type} [Finite ι] (Ω : S.Opens) (e : ι → Γ(S, Ω)) (x : S) (hxΩ : x ∈ Ω)
    (hxV : g.base x ∈ V) (hc : IsClosed ({x} : Set S))
    (hsurj : Function.Surjective (g.stalkMap x)) :
    ∃ O : S.Opens, x ∈ O ∧ O ≤ Ω ⊓ g ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial σ ℂ) (F : ι → MvPolynomial σ ℂ),
        eval (fun a => val t (u a) (g.base x) hxV) q ≠ 0 ∧
        ∀ (y : S) (hyΩ : y ∈ Ω) (hyV : g.base y ∈ V), y ∈ O → IsClosed ({y} : Set S) →
          eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 ∧
          ∀ i, val s (e i) y hyΩ * eval (fun a => val t (u a) (g.base y) hyV) q =
            eval (fun a => val t (u a) (g.base y) hyV) (F i) := by
  classical
  cases nonempty_fintype ι
  let z : V := ⟨g.base x, hxV⟩
  let : Algebra Γ(T, V) (T.presheaf.stalk (g.base x)) :=
    TopCat.Presheaf.algebra_section_stalk T.presheaf z
  have : IsLocalization.AtPrime (T.presheaf.stalk (g.base x)) (hV.primeIdealOf z).asIdeal :=
    hV.isLocalization_stalk z
  have hw : ∀ i, ∃ w : T.presheaf.stalk (g.base x),
      g.stalkMap x w = S.presheaf.germ Ω x hxΩ (e i) := fun i => hsurj _
  choose w hw using hw
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (hV.primeIdealOf z).asIdeal.primeCompl w
  have hint' : ∀ i, ∃ a : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) a = b • w i :=
    fun i => hint i
  choose a ha using hint'
  have halg : ∀ c : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) c =
      T.presheaf.germ V (g.base x) hxV c := fun c => rfl
  have hunit : IsUnit (T.presheaf.germ V (g.base x) hxV b) := by
    rw [← halg]
    exact IsLocalization.map_units (T.presheaf.stalk (g.base x))
      (⟨b, hb⟩ : (hV.primeIdealOf z).asIdeal.primeCompl)
  let Ω' : S.Opens := Ω ⊓ g ⁻¹ᵁ V
  have hΩ'V : Ω' ≤ g ⁻¹ᵁ V := inf_le_right
  have hΩ'Ω : Ω' ≤ Ω := inf_le_left
  have hxΩ' : x ∈ Ω' := ⟨hxΩ, hxV⟩
  have hgerm : ∀ c : Γ(T, V), S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V c) =
      g.stalkMap x (T.presheaf.germ V (g.base x) hxV c) := by
    intro c
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  have hEq : ∀ i, S.presheaf.germ Ω' x hxΩ'
      (g.appLE V Ω' hΩ'V b * S.presheaf.map (homOfLE hΩ'Ω).op (e i)) =
      S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V (a i)) := by
    intro i
    rw [map_mul, hgerm, hgerm, TopCat.Presheaf.germ_res_apply, ← hw i, ← map_mul]
    congr 1
    rw [← halg, ← halg, ha i, Algebra.smul_def]
  have hO := fun i => TopCat.Presheaf.germ_eq S.presheaf x hxΩ' hxΩ' _ _ (hEq i)
  choose Oi hxOi iU iV hOi using hO
  obtain ⟨q, hq⟩ := hu b
  choose F hF using fun i => hu (a i)
  let O : S.Opens := (g ⁻¹ᵁ T.basicOpen b) ⊓ Ω' ⊓ Finset.univ.inf Oi
  have hmemO : ∀ y, y ∈ O → y ∈ g ⁻¹ᵁ T.basicOpen b ∧ y ∈ Ω' ∧ ∀ i, y ∈ Oi i := by
    intro y hy
    refine ⟨hy.1.1, hy.1.2, fun i => ?_⟩
    have h2 := hy.2
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf] at h2
    simp only [Set.iInf_eq_iInter, Set.mem_iInter] at h2
    exact h2 i (Finset.mem_univ i)

  have hne : ∀ (y : S) (hyV : g.base y ∈ V), IsClosed ({y} : Set S) →
      g.base y ∈ T.basicOpen b → eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 := by
    intro y hyV hcy hyb
    have hcy' := isClosed_image_of_closed s t g hg y hcy
    rw [← val_eval₂ t u q _ hyV hcy', ← hq]
    intro h0
    rw [val_eq_zero_iff t b _ hyV hcy', ← Scheme.germ_residue, CommRingCat.comp_apply] at h0
    have hu' := (T.mem_basicOpen b (g.base y) hyV).mp hyb
    exact (hu'.map (T.residue (g.base y)).hom).ne_zero h0
  refine ⟨O, ?_, fun y hy => (hmemO y hy).2.1, q, F, ?_, ?_⟩
  · refine ⟨⟨?_, hxΩ'⟩, ?_⟩
    · exact (T.mem_basicOpen b (g.base x) hxV).mpr hunit
    · show x ∈ ((Finset.univ.inf Oi : S.Opens) : Set S)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
      simp only [Set.iInf_eq_iInter, Set.mem_iInter]
      exact fun i _ => hxOi i
  · exact hne x hxV hc ((T.mem_basicOpen b (g.base x) hxV).mpr hunit)
  · intro y hyΩ hyV hyO hcy
    obtain ⟨hyb, hyΩ', hyOi⟩ := hmemO y hyO
    have hcy' := isClosed_image_of_closed s t g hg y hcy
    refine ⟨hne y hyV hcy hyb, fun i => ?_⟩
    obtain ⟨φ, hφ⟩ := val_ringHom s Ω' y hyΩ' hcy
    have h1 := congrArg (fun f => val s f y (hyOi i)) (hOi i)
    simp only at h1
    rw [show iU i = homOfLE (leOfHom (iU i)) from rfl, show iV i = homOfLE (leOfHom (iV i)) from rfl,
      val_restrict, val_restrict, ← hφ, map_mul, hφ, hφ, val_restrict] at h1
    rw [(val_comp s t g hg hΩ'V b y hyΩ' hcy).2, (val_comp s t g hg hΩ'V (a i) y hyΩ' hcy).2] at h1
    have e1 : val t b (g.base y) (hΩ'V hyΩ') = eval (fun a => val t (u a) (g.base y) hyV) q := by
      rw [hq]; exact val_eval₂ t u q _ hyV hcy'
    have e2 : val t (a i) (g.base y) (hΩ'V hyΩ') =
        eval (fun a => val t (u a) (g.base y) hyV) (F i) := by
      rw [hF i]; exact val_eval₂ t u (F i) _ hyV hcy'
    rw [e1, e2] at h1
    rw [mul_comm]
    exact h1

end

end ReciprocityTheory.AnForm.R
end

