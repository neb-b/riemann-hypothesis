module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ComplexPointEvalPullbackSection
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

theorem UpperTheory.complexPoint_eval_pullback_section :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z) (h : c ≫ s = s') (V : Z.Opens) (f : Γ(Z, V)) (y : CxPts s' (RingHom.id ℂ)), y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c ⁻¹ᵁ V) → CxPts.ev s' (RingHom.id ℂ) (c ⁻¹ᵁ V) ((c.app V).hom f) y = CxPts.ev s (RingHom.id ℂ) V f (UpperTheory.A.zpt c h y) := by
  intro Z Y s s' c h V f y _
  exact (GlobalTheory.Points.valR_comp y.1 c V f).symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ComplexPointsBijectiveAlgHomAffineOpen
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.TopForm ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi in
private theorem germ_algX {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (V : X.Opens) (hg : genericPoint X ∈ V) (a : ℂ) :
    (X.presheaf.germ V (genericPoint X) hg).hom (algX p V a) = @algebraMap ℂ X.functionField _ _ (ffAlg p) a := by
  have h := congrArg (fun φ => φ a) (GlobalTheory.TopForm.resG_comp_algX p (le_top : V ≤ ⊤))
  simp only [RingHom.comp_apply] at h
  rw [← h]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG, TopCat.Presheaf.germ_res_apply]
  simp only [algX, GlobalTheory.PD.ffAlg, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, Scheme.Hom.appLE]
  simp only [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  rfl

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue in
theorem UpperTheory.complexPoints_bijective_algHom_affineOpen :
    ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) [inst : Algebra ℂ X.functionField], inst = ffAlg p → ∀ (V : X.Opens), IsAffineOpen V → ∀ (hg : genericPoint X ∈ V) (B : Subalgebra ℂ X.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hg).hom f = y) → (∀ e : B →ₐ[ℂ] ℂ, ∃! y : CxPts p (RingHom.id ℂ), UpperTheory.A.Mt p V hg B e y) ∧ (∀ y ∈ CxPts.ptsIn p (RingHom.id ℂ) V, ∃! e : B →ₐ[ℂ] ℂ, UpperTheory.A.Mt p V hg B e y) := by
  intro X _ p inst hinst V hV hg B hB
  subst hinst
  set g := (X.presheaf.germ V (genericPoint X) hg).hom with hgdef
  have ginj : Function.Injective g := germ_injective_of_isIntegral X (genericPoint X) hg
  have gB : ∀ f, g f ∈ B := fun f => (hB _).2 ⟨f, rfl⟩
  let gr : Γ(X, V) →+* B := g.codRestrict B gB
  have grbij : Function.Bijective gr := by
    refine ⟨fun x y hxy => ginj (congrArg Subtype.val hxy), fun b => ?_⟩
    obtain ⟨f, hf⟩ := (hB b.1).1 b.2
    exact ⟨f, Subtype.ext hf⟩
  let eqv : Γ(X, V) ≃+* B := RingEquiv.ofBijective gr grbij
  have eqv_apply : ∀ f, eqv f = ⟨g f, gB f⟩ := fun f => rfl
  have alg_eq : ∀ a : ℂ, (algebraMap ℂ B a) = eqv (algX p V a) := by
    intro a
    apply Subtype.ext
    rw [eqv_apply]
    exact (germ_algX p V hg a).symm
  constructor
  · intro e
    let φ : Γ(X, V) →+* ℂ := (e : B →+* ℂ).comp (eqv : Γ(X, V) →+* B)
    have hφ : ∀ a : ℂ, φ (algX p V a) = RingHom.id ℂ a := by
      intro a
      change e (eqv (algX p V a)) = a
      rw [← alg_eq]
      exact e.commutes a
    refine ⟨CxPts.ofHom hV φ hφ, ⟨CxPts.ofHom_mem hV φ hφ, fun f hf => ?_⟩, ?_⟩
    · rw [CxPts.ev_ofHom]
      rfl
    · rintro y ⟨hy, hye⟩
      apply Subtype.ext
      apply GlobalTheory.Points.ext_of_valR hV hy (CxPts.ofHom_mem hV φ hφ)
      intro f
      change CxPts.ev p (RingHom.id ℂ) V f y = CxPts.ev p (RingHom.id ℂ) V f (CxPts.ofHom hV φ hφ)
      rw [CxPts.ev_ofHom, ← hye f (gB f)]
      rfl
  · intro y hy
    let e0 : B →+* ℂ := (CxPts.evHom hy).comp (eqv.symm : B →+* Γ(X, V))
    have he0 : ∀ a : ℂ, e0 (algebraMap ℂ B a) = algebraMap ℂ ℂ a := by
      intro a
      change CxPts.evHom hy (eqv.symm (algebraMap ℂ B a)) = a
      rw [alg_eq, RingEquiv.symm_apply_apply, ← CxPts.ev_eq hy, CxPts.ev_algX hy]
      rfl
    let e : B →ₐ[ℂ] ℂ := { e0 with commutes' := he0 }
    refine ⟨e, ⟨hy, fun f hf => ?_⟩, ?_⟩
    · change CxPts.evHom hy (eqv.symm ⟨g f, hf⟩) = _
      rw [show (⟨g f, hf⟩ : B) = eqv f from rfl, RingEquiv.symm_apply_apply, CxPts.ev_eq hy]
    · rintro e' ⟨_, he'⟩
      apply AlgHom.ext
      intro b
      obtain ⟨f, hf⟩ := (hB b.1).1 b.2
      have hb : b = ⟨g f, gB f⟩ := Subtype.ext hf.symm
      subst hb
      rw [he' f (gB f)]
      change _ = CxPts.evHom hy (eqv.symm (eqv f))
      rw [RingEquiv.symm_apply_apply, CxPts.ev_eq hy]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceDifferentialsStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

theorem UpperTheory.etaleCorrespondence_differentials_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)) (l : Fin d) (hg : genericPoint Y ∈ c1 ⁻¹ᵁ U l.succ) (hg0 : genericPoint Y ∈ c1 ⁻¹ᵁ U 0) (e : rB ℂ Y.functionField x {l.succ} →ₐ[ℂ] ℂ) (e0 : rB ℂ Y.functionField x {0} →ₐ[ℂ] ℂ) (y : CxPts s' (RingHom.id ℂ)), UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U l.succ) hg _ e y → UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) hg0 _ e0 y → e0 ⟨_, tco_mem ℂ Y.functionField x l⟩ ≠ 0 := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU l hg hg0 e e0 y hM hM0
  have mem : ∀ (I : Finset (Fin (d + 1))) (i j : Fin (d + 1)), i ∈ I →
      algebraMap F Y.functionField (x j / x i) ∈ rB ℂ Y.functionField x I := fun I i j hi =>
    (integralClosure (rA ℂ x I) Y.functionField).algebraMap_mem
      ⟨x j / x i, Algebra.subset_adjoin ⟨i, hi, j, rfl⟩⟩
  obtain ⟨f0, hf0⟩ := (UpperTheory.A.mem_rB_pull h1 hK hL g1 hU {0} ⟨0, by simp⟩ (c1 ⁻¹ᵁ U 0) (by simp) hg0 _).1
    (tco_mem ℂ Y.functionField x l)
  have hV : genericPoint Y ∈ c1 ⁻¹ᵁ U 0 ⊓ c1 ⁻¹ᵁ U l.succ := ⟨hg0, hg⟩
  obtain ⟨fb, hfb⟩ := (UpperTheory.A.mem_rB_pull h1 hK hL g1 hU {0, l.succ} ⟨0, by simp⟩
    (c1 ⁻¹ᵁ U 0 ⊓ c1 ⁻¹ᵁ U l.succ) (by simp) hV _).1 (mem _ l.succ 0 (by simp))
  have hres : (Y.presheaf.germ _ (genericPoint Y) hV).hom (resG Y inf_le_left f0) =
      algebraMap F Y.functionField (x l.succ / x 0) := by
    rw [← hf0]
    exact Y.presheaf.germ_res_apply (homOfLE inf_le_left) (genericPoint Y) hV f0
  have hne := hx.pd.ne
  have hunit : resG Y inf_le_left f0 * fb = 1 := by
    apply germ_injective_of_isIntegral Y (genericPoint Y) hV
    rw [map_mul, map_one, hres, hfb, ← map_mul, div_mul_div_comm, mul_comm (x l.succ), div_self (mul_ne_zero (hne _) (hne _)), map_one]
  have hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0 ⊓ c1 ⁻¹ᵁ U l.succ) :=
    CxPts.mem_ptsIn_inf.2 ⟨hM0.1, hM.1⟩
  have hval := hM0.2 f0 (hf0 ▸ tco_mem ℂ Y.functionField x l)
  have h3 : e0 ⟨_, tco_mem ℂ Y.functionField x l⟩ = CxPts.ev s' (RingHom.id ℂ) _ f0 y := by
    rw [← hval]; congr 2; exact hf0.symm
  rw [h3, ← CxPts.ev_res inf_le_left hy f0]
  exact CxPts.ev_ne_zero hy (IsUnit.of_mul_eq_one _ hunit)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFieldExtensionStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

private theorem red_of_fu {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Algebra A B]
    [IsScalarTower ℂ A B] [Algebra.FormallyUnramified A B] (I : Ideal A) [IsReduced (A ⧸ I)]
    [Module.Finite ℂ (A ⧸ I)] [Module.Finite ℂ (B ⧸ I.map (algebraMap A B))] :
    IsReduced (B ⧸ I.map (algebraMap A B)) := by
  have h1 : Algebra.FormallyUnramified ℂ (A ⧸ I) := GlobalTheory.SepIdem.formallyUnramified_of_isReduced ℂ _
  have h2 : Algebra.FormallyUnramified A (B ⧸ I.map (algebraMap A B)) := by
    haveI : Algebra.FormallyUnramified B (B ⧸ I.map (algebraMap A B)) :=
      .of_surjective (Ideal.Quotient.mkₐ B _) Ideal.Quotient.mk_surjective
    exact .comp A B _
  have h3 : Algebra.FormallyUnramified (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    .of_restrictScalars A _ _
  haveI : IsScalarTower ℂ (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := .of_algebraMap_eq fun c => by
    have e : algebraMap ℂ (B ⧸ I.map (algebraMap A B)) c =
        algebraMap B (B ⧸ I.map (algebraMap A B)) (algebraMap A B (algebraMap ℂ A c)) := by
      rw [← IsScalarTower.algebraMap_apply ℂ A B, ← IsScalarTower.algebraMap_apply ℂ B _]
    rw [e, IsScalarTower.algebraMap_apply ℂ A (A ⧸ I)]
    rfl
  have h4 : Algebra.FormallyUnramified ℂ (B ⧸ I.map (algebraMap A B)) := .comp ℂ (A ⧸ I) _
  exact Algebra.FormallyUnramified.isReduced_of_field ℂ _

private theorem fin_of_const {R E Q : Type} [CommRing R] [CommRing E] [Algebra R E] [Module.Finite R E] [CommRing Q]
    [Algebra ℂ Q] (φ : R →+* Q) (π : E →+* Q) (hs : Function.Surjective π) (hπ : ∀ r e, π (r • e) = φ r * π e)
    (hc : ∀ r, ∃ c : ℂ, φ r = algebraMap ℂ Q c) : Module.Finite ℂ Q := by
  obtain ⟨n, s, hs'⟩ := Module.Finite.exists_fin (R := R) (M := E)
  have key : ∀ e, π e ∈ Submodule.span ℂ (Set.range (π ∘ s)) := by
    intro e
    have he : e ∈ Submodule.span R (Set.range s) := hs' ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ iha ihb => rw [map_add (f := _)]; exact Submodule.add_mem _ iha ihb
    | smul r y _ ih =>
      obtain ⟨c, hc'⟩ := hc r
      rw [hπ, hc', ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ ih
  have htop : Submodule.span ℂ (Set.range (π ∘ s)) = ⊤ := by
    refine top_le_iff.1 fun a _ => ?_
    obtain ⟨b, rfl⟩ := hs a
    exact key b
  exact ⟨htop ▸ Submodule.fg_span (Set.finite_range _)⟩

private theorem rA_const {F Q : Type} [Field F] [Algebra ℂ F] [CommRing Q] [Algebra ℂ Q] {d : ℕ} (x : Fin (d + 1) → F)
    (h0 : x 0 ≠ 0) (ψ : rA ℂ x {0} →ₐ[ℂ] Q) (ht : ∀ (j : Fin d) (h : x j.succ / x 0 ∈ rA ℂ x {0}), ψ ⟨_, h⟩ = 0)
    (r : rA ℂ x {0}) : ∃ c : ℂ, ψ r = algebraMap ℂ Q c := by
  obtain ⟨r, hr⟩ := r
  induction hr using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, j, rfl⟩ := hy
    rw [Finset.mem_singleton] at hi
    subst hi
    induction j using Fin.cases with
    | zero =>
      refine ⟨1, ?_⟩
      rw [map_one, ← map_one ψ]
      congr 1
      exact Subtype.ext (div_self h0)
    | succ j => exact ⟨0, by rw [map_zero]; exact ht j _⟩
  | algebraMap c => exact ⟨c, ψ.commutes c⟩
  | add a b ha hb iha ihb =>
    obtain ⟨c₁, e₁⟩ := iha
    obtain ⟨c₂, e₂⟩ := ihb
    exact ⟨c₁ + c₂, by rw [map_add (f := _), ← e₁, ← e₂]; exact map_add ψ ⟨a, ha⟩ ⟨b, hb⟩⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨c₁, e₁⟩ := iha
    obtain ⟨c₂, e₂⟩ := ihb
    exact ⟨c₁ * c₂, by rw [map_mul, ← e₁, ← e₂]; exact map_mul ψ ⟨a, ha⟩ ⟨b, hb⟩⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
private theorem fin_quot {K F : Type} [Field K] [Field F] [Algebra ℂ K] [Algebra ℂ F] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (hx : IsFinCover ℂ K x) :
    Module.Finite ℂ ((rB ℂ K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})))) := by
  set J := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})) with hJ
  let φ : rA ℂ x {0} →ₐ[ℂ] rB ℂ K x {0} :=
    { toFun := fun a => ⟨algebraMap F K a, (integralClosure (rA ℂ x {0}) K).algebraMap_mem a⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _)
      commutes' := fun c => Subtype.ext (IsScalarTower.algebraMap_apply ℂ F K c).symm }
  let ψ : rA ℂ x {0} →ₐ[ℂ] (rB ℂ K x {0} ⧸ J) := (Ideal.Quotient.mkₐ ℂ J).comp φ
  have hψ := rA_const x (hx.pd.ne 0) ψ fun j h =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
  let ι : integralClosure (rA ℂ x {0}) K →+* rB ℂ K x {0} :=
    { toFun := fun e => ⟨e.1, e.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  haveI hfin : Module.Finite (rA ℂ x {0}) (integralClosure (rA ℂ x {0}) K) :=
    rA_finite hx (Finset.mem_singleton_self 0)
  refine fin_of_const (R := rA ℂ x {0}) (E := integralClosure (rA ℂ x {0}) K) ψ.toRingHom
    ((Ideal.Quotient.mk J).comp ι) ?_ ?_ hψ
  · intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨⟨b.1, b.2⟩, rfl⟩
  · intro r e
    have e0 : ι (r • e) = φ r * ι e := Subtype.ext (Algebra.smul_def r (e : K))
    change Ideal.Quotient.mk J (ι (r • e)) = Ideal.Quotient.mk J (φ r) * Ideal.Quotient.mk J (ι e)
    rw [e0, map_mul]

private noncomputable def upB (K L : Type) {F : Type} [Field K] [Field L] [Field F] [Algebra ℂ K] [Algebra ℂ L] [Algebra ℂ F]
    [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower ℂ F K] [IsScalarTower ℂ F L] [IsScalarTower ℂ K L]
    [IsScalarTower F K L] {d : ℕ} (x : Fin (d + 1) → F) : rB ℂ K x {0} →ₐ[ℂ] rB ℂ L x {0} :=
  { toFun := fun b => ⟨algebraMap K L b, by
      haveI : IsScalarTower (rA ℂ x {0}) K L := .of_algebraMap_eq fun a => by
        change algebraMap F L a = algebraMap K L (algebraMap F K a)
        exact IsScalarTower.algebraMap_apply F K L _
      have hb : IsIntegral (rA ℂ x {0}) (b : K) := b.2
      exact hb.algebraMap⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun a b => Subtype.ext (map_add _ _ _)
    commutes' := fun c => Subtype.ext (IsScalarTower.algebraMap_apply ℂ K L c).symm }

private theorem map_upB_span_tco (K L : Type) {F : Type} [Field K] [Field L] [Field F] [Algebra ℂ K] [Algebra ℂ L] [Algebra ℂ F]
    [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower ℂ F K] [IsScalarTower ℂ F L] [IsScalarTower ℂ K L]
    [IsScalarTower F K L] {d : ℕ} (x : Fin (d + 1) → F) :
    (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0}))).map (upB K L x).toRingHom =
      Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ L x j⟩ : rB ℂ L x {0})) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact Subtype.ext (IsScalarTower.algebraMap_apply F K L _).symm


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
private theorem upB_fu {d : ℕ} {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ}
    [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] {c : Y ⟶ Z} (h : c ≫ s = s') [IsFinite c] [Etale c]
    [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s')
    [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField]
    (g : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g))
    {F : Type} [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField]
    [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField]
    (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hU : IsAffCover s U (rB ℂ Z.functionField x)) :
    (upB Z.functionField Y.functionField x).toRingHom.FormallyUnramified := by
  have hne : ({0} : Finset (Fin (d + 1))).Nonempty := ⟨0, by simp⟩
  obtain ⟨V, hVdef⟩ : ∃ V, V = ({0} : Finset (Fin (d + 1))).inf U := ⟨_, rfl⟩
  have hV : genericPoint Z ∈ V := hVdef ▸ hU.ne {0}
  have hV' : genericPoint Y ∈ c ⁻¹ᵁ V := by
    change c (genericPoint Y) ∈ V
    rw [UpperTheory.A.generic_map c]
    exact hV
  have hVa : IsAffineOpen V := hVdef ▸ hU.affine {0} hne
  have hVa' : IsAffineOpen (c ⁻¹ᵁ V) := hVa.preimage c
  have het : (c.app V).hom.Etale := by
    have := Etale.etale_appLE (f := c) hVa hVa' le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  have hfu : (c.app V).hom.FormallyUnramified := het.formallyUnramified
  have memK : ∀ y, y ∈ rB ℂ Z.functionField x {0} ↔ ∃ f : Γ(Z, V), (Z.presheaf.germ V (genericPoint Z) hV).hom f = y := by
    subst hVdef
    exact hU.ring {0} hne
  have memL : ∀ y, y ∈ rB ℂ Y.functionField x {0} ↔ ∃ f : Γ(Y, c ⁻¹ᵁ V), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom f = y :=
    UpperTheory.A.mem_rB_pull h hK hL g hU {0} hne (c ⁻¹ᵁ V) (by rw [UpperTheory.A.preimage_inf, hVdef]) hV'
  let aK : Γ(Z, V) →+* rB ℂ Z.functionField x {0} :=
    (Z.presheaf.germ V (genericPoint Z) hV).hom.codRestrict _ fun f => (memK _).2 ⟨f, rfl⟩
  let aL : Γ(Y, c ⁻¹ᵁ V) →+* rB ℂ Y.functionField x {0} :=
    (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom.codRestrict _ fun f => (memL _).2 ⟨f, rfl⟩
  have bK : Function.Bijective aK := by
    refine ⟨fun a b e => germ_injective_of_isIntegral Z _ hV (congrArg Subtype.val e), fun y => ?_⟩
    obtain ⟨f, hf⟩ := (memK y.1).1 y.2
    exact ⟨f, Subtype.ext hf⟩
  have bL : Function.Bijective aL := by
    refine ⟨fun a b e => germ_injective_of_isIntegral Y _ hV' (congrArg Subtype.val e), fun y => ?_⟩
    obtain ⟨f, hf⟩ := (memL y.1).1 y.2
    exact ⟨f, Subtype.ext hf⟩
  let eK := RingEquiv.ofBijective aK bK
  let eL := RingEquiv.ofBijective aL bL
  have hcomm : (upB Z.functionField Y.functionField x).toRingHom = (eL.toRingHom.comp (c.app V).hom).comp eK.symm.toRingHom := by
    refine RingHom.ext fun y => ?_
    obtain ⟨f, rfl⟩ := eK.surjective y
    refine Subtype.ext ?_
    have e1 : eK.symm (eK f) = f := eK.symm_apply_apply f
    change algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom f) =
      (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom (eK.symm (eK f)))
    rw [e1, g V hV hV' f]
  rw [hcomm]
  exact RingHom.FormallyUnramified.respectsIso.2 _ _ (RingHom.FormallyUnramified.respectsIso.1 _ _ hfu)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem UpperTheory.etaleCorrespondence_fieldExtension_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)), IsReduced ((rB ℂ Z.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Z.functionField x j⟩ : rB ℂ Z.functionField x {0})))) → IsReduced ((rB ℂ Y.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Y.functionField x j⟩ : rB ℂ Y.functionField x {0})))) := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU hred
  obtain ⟨hxL, -⟩ := UpperTheory.A.isFinCover_pull h1 hK hL g1 hx hU
  have hfu := upB_fu h1 hK hL g1 x U hU
  letI alg : Algebra (rB ℂ Z.functionField x {0}) (rB ℂ Y.functionField x {0}) :=
    (upB Z.functionField Y.functionField x).toRingHom.toAlgebra
  haveI : Algebra.FormallyUnramified (rB ℂ Z.functionField x {0}) (rB ℂ Y.functionField x {0}) := hfu
  haveI : IsScalarTower ℂ (rB ℂ Z.functionField x {0}) (rB ℂ Y.functionField x {0}) :=
    .of_algebraMap_eq fun c => ((upB Z.functionField Y.functionField x).commutes c).symm
  have hI := map_upB_span_tco Z.functionField Y.functionField x
  haveI := fin_quot x hx
  have hfinL := fin_quot x hxL
  rw [← hI] at hfinL ⊢
  exact red_of_fu _
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFunctionFieldStatementOne
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

set_option autoImplicit false

private theorem isIntegral_map_iff {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (B : Subalgebra ℂ K) (y : L) :
    IsIntegral (B.map (IsScalarTower.toAlgHom ℂ K L)) y ↔ IsIntegral B y := by
  let j := IsScalarTower.toAlgHom ℂ K L
  let e : B →+* B.map j := (B.equivMapOfInjective j j.toRingHom.injective).toAlgHom.toRingHom
  letI : Algebra B (B.map j) := e.toAlgebra
  haveI : IsScalarTower B (B.map j) L := .of_algebraMap_eq fun a => rfl
  haveI : Algebra.IsIntegral B (B.map j) := ⟨fun b => by
    obtain ⟨a, rfl⟩ := (B.equivMapOfInjective j j.toRingHom.injective).surjective b
    exact isIntegral_algebraMap (x := a)⟩
  exact ⟨fun h => isIntegral_trans y h, fun h => h.tower_top⟩

private theorem dualNumberPoint_preimage_top_of_reduction {d : ℕ} {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ}
    [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] {c : Y ⟶ Z} (hc : c ≫ s = s') [IsFinite c] [Etale c]
    [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s')
    (j : Z.functionField →ₐ[ℂ] Y.functionField)
    (hj : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
      j ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g))
    {F : Type} [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [IsScalarTower ℂ F Z.functionField]
    (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x)
    (hU : IsAffCover s U (rB ℂ Z.functionField x)) :
    IsAffCover s' (fun i => c ⁻¹ᵁ U i) (R2 x j) := by
  letI : Algebra Z.functionField Y.functionField := j.toRingHom.toAlgebra
  letI : Algebra F Y.functionField :=
    ((algebraMap Z.functionField Y.functionField).comp (algebraMap F Z.functionField)).toAlgebra
  haveI : IsScalarTower ℂ Z.functionField Y.functionField := .of_algebraMap_eq fun r => (j.commutes r).symm
  haveI : IsScalarTower F Z.functionField Y.functionField := .of_algebraMap_eq fun r => rfl
  haveI : IsScalarTower ℂ F Y.functionField := .of_algebraMap_eq fun r => by
    change algebraMap ℂ Y.functionField r = j (algebraMap F Z.functionField (algebraMap ℂ F r))
    rw [← IsScalarTower.algebraMap_apply ℂ F Z.functionField, j.commutes]
  have hjeq : IsScalarTower.toAlgHom ℂ Z.functionField Y.functionField = j := AlgHom.ext fun _ => rfl
  have e : rB ℂ Y.functionField x = R2 x j := by
    funext I
    ext y
    change IsIntegral (rA ℂ x I) y ↔ IsIntegral ((rB ℂ Z.functionField x I).map j) y
    rw [UpperTheory.A.isIntegral_rB_iff (K := Z.functionField) x I y, ← hjeq, isIntegral_map_iff]
  rw [← e]
  exact (UpperTheory.A.isFinCover_pull hc hK hL (fun V hV hV' g => (hj V hV hV' g).symm) hx hU).2

theorem UpperTheory.etaleCorrespondence_functionField_statement_one :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)), IsAffCover s' (fun i => c2 ⁻¹ᵁ U i) (R2 x j2) := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU
  exact dualNumberPoint_preimage_top_of_reduction h2 hK hL j2 g2 x U hx hU
end

