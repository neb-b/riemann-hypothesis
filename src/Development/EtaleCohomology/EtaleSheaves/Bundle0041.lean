module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0028
public import Development.EtaleCohomology.EtaleSheaves.Bundle0022
public import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.LevelsOfGen
public import Development.EtaleCohomology.EtaleSheaves.Bundle0017
public import Development.EtaleCohomology.EtaleSheaves.Bundle0024
public import Development.EtaleCohomology.EtaleSheaves.Bundle0031

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.RelNormPfAff
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

open AlgebraicGeometry.Scheme.Hom in
theorem closedAt_preimage {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g]
    (U : S.Opens) (hU : IsAffineOpen U) : ClosedAt g.toNormalization (g.fromNormalization ⁻¹ᵁ U) := by
  intro b hb
  letI := (g.app U).hom.toAlgebra
  have hle : g ⁻¹ᵁ U ≤ g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U := by
    simp [← Scheme.Hom.comp_preimage]
  have hle' : g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U ≤ g ⁻¹ᵁ U := by
    simp [← Scheme.Hom.comp_preimage]
  set ρ := Z.presheaf.map (homOfLE hle).op with hρ
  have key := g.normalizationObjIso_hom_val hU
  have hρinj : Function.Injective ρ := by
    intro u v huv
    have := congrArg (Z.presheaf.map (homOfLE hle').op) huv
    have h1 : (homOfLE hle).op ≫ (homOfLE hle').op = 𝟙 (Opposite.op (g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U)) :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    simpa [hρ, ← CommRingCat.comp_apply, ← Functor.map_comp, h1] using this

  have hint : IsIntegral (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) (ρ b) := by
    obtain ⟨p, hm, hp⟩ := hb
    refine ⟨p.map (g.normalizationObjIso hU).hom.hom, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) Γ(Z, g ⁻¹ᵁ U)).comp
        (g.normalizationObjIso hU).hom.hom = ρ.hom.comp (g.toNormalization.app _).hom := by
      have := congrArg CommRingCat.Hom.hom key
      rw [Scheme.Hom.appLE] at this
      exact this
    rw [e, ← Polynomial.hom_eval₂, hp, map_zero]
  have hmem : ρ b ∈ (⊥ : Subalgebra (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) Γ(Z, g ⁻¹ᵁ U)) := by
    rw [← integralClosure_idem]; exact hint
  obtain ⟨z, hz⟩ := Algebra.mem_bot.mp hmem
  refine ⟨(g.normalizationObjIso hU).inv z, hρinj ?_⟩
  have := congrArg (fun φ => φ ((g.normalizationObjIso hU).inv z)) (congrArg CommRingCat.Hom.hom key)
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [← this, ← hz]
  simp

end LateralTheory.E.RelNormPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RootPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.RootPf

lemma unit_sec {Z : Scheme.{0}} (q : ℕ) (A : Type) [CommRing A] (p : Z ⟶ Spec (CommRingCat.of A))
    (hq : IsUnit (q : A)) (U : Z.Opens) : IsUnit (q : Γ(Z, U)) := by
  let f : CommRingCat.of A ⟶ Γ(Z, U) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top).op
  have := hq.map f.hom
  simpa using this

lemma prim_of_aic (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] (hT : AIC T)
    (hq : IsUnit (q : T)) : ∃ a : T, IsPrimitiveRoot a q := by
  have : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨a, ha⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  exact ⟨a, (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := a)).1 ha⟩

lemma local_root {Z : Scheme.{0}} [IsIntegral Z]
    (hZ : ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → AIC Γ(Z, U))
    (q : ℕ) [NeZero q] (hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U))) (ζ : Z.functionField)
    (hζ : IsPrimitiveRoot ζ q) (V : Z.Opens) (hV : IsAffineOpen V) [hne : Nonempty V] :
    ∃ s : Γ(Z, V), (Z.germToFunctionField V).hom s = ζ := by
  obtain ⟨a, ha⟩ := prim_of_aic q Γ(Z, V)
    (hZ V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)) (hqU V)
  have hb := ha.map_of_injective (f := (Z.germToFunctionField V).hom) (Z.germToFunctionField_injective V)
  obtain ⟨i, -, hi⟩ := hb.eq_pow_of_pow_eq_one hζ.pow_eq_one
  exact ⟨a ^ i, by rw [map_pow]; exact hi⟩

theorem Root_of : LateralTheory.E.ChartSurjCut.Root := by
  intro q A _ Z p hZ hq
  obtain ⟨hI, hA⟩ := hZ
  have hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U)) := fun U => unit_sec q A p hq U
  obtain ⟨x⟩ := (inferInstance : Nonempty Z)
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨x, trivial⟩⟩
  have hq0 : NeZero q := ⟨by rintro rfl; exact not_isUnit_zero (M₀ := Γ(Z, ⊤)) (by simpa using hqU ⊤)⟩
  have hbasis : ∀ {U : Z.Opens} {y : Z}, y ∈ U → ∃ U' ∈ Z.affineOpens, y ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
  have haff : ∀ y : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ y ∈ U := by
    intro y
    obtain ⟨U, hU, hy, -⟩ := hbasis (show y ∈ (⊤ : Z.Opens) from trivial)
    exact ⟨U, hU, hy⟩
  obtain ⟨U₀, hU₀, hx⟩ := haff x
  have : Nonempty U₀ := ⟨⟨x, hx⟩⟩
  obtain ⟨a₀, ha₀⟩ := prim_of_aic q Γ(Z, U₀) (hA U₀ hU₀ ⟨x, hx⟩) (hqU U₀)
  set ζ : Z.functionField := (Z.germToFunctionField U₀).hom a₀ with hζdef
  have hζ : IsPrimitiveRoot ζ q :=
    ha₀.map_of_injective (f := (Z.germToFunctionField U₀).hom) (Z.germToFunctionField_injective U₀)
  let ι := {V : Z.Opens // IsAffineOpen V ∧ Nonempty V}
  let U : ι → Z.Opens := fun i => i.1
  have instU : ∀ i : ι, Nonempty (U i) := fun i => i.2.2
  have hex : ∀ i : ι, ∃ s : Γ(Z, U i), (Z.germToFunctionField (U i)).hom s = ζ := fun i =>
    @local_root Z hI hA q hq0 hqU ζ hζ i.1 i.2.1 i.2.2
  let sf : ∀ i : ι, Γ(Z, U i) := fun i => Classical.choose (hex i)
  have hsf : ∀ i : ι, (Z.germToFunctionField (U i)).hom (sf i) = ζ := fun i => Classical.choose_spec (hex i)
  have hcov : (⊤ : Z.Opens) ≤ iSup U := by
    intro y _
    obtain ⟨V, hV, hy⟩ := haff y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, ⟨⟨y, hy⟩⟩⟩, hy⟩
  have hcomp : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have : Nonempty (U i ⊓ U j : Z.Opens) := by
      obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (U i).isOpen (U j).isOpen
        (by obtain ⟨⟨y, hy⟩⟩ := i.2.2; exact ⟨y, hy⟩) (by obtain ⟨⟨y, hy⟩⟩ := j.2.2; exact ⟨y, hy⟩)
      exact ⟨⟨y, hy⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf i)) = Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact (hsf i).trans (hsf j).symm
  obtain ⟨s0, hs, -⟩ := Z.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcov sf hcomp
  let s : Γ(Z, ⊤) := s0
  change ∀ i : ι, Z.presheaf.map (homOfLE le_top).op s = sf i at hs
  have hgs : (Z.germToFunctionField ⊤).hom s = ζ := by
    have h1 := hs ⟨U₀, hU₀, inferInstance⟩
    have h2 := hsf ⟨U₀, hU₀, inferInstance⟩
    rw [← h1] at h2
    change Z.presheaf.germ _ _ _ (Z.presheaf.map _ s) = ζ at h2
    rw [TopCat.Presheaf.germ_res_apply] at h2
    exact h2
  have hps : IsPrimitiveRoot s q := by
    have h' : IsPrimitiveRoot ((Z.germToFunctionField ⊤).hom s) q := by rw [hgs]; exact hζ
    exact IsPrimitiveRoot.of_map_of_injective h' (Z.germToFunctionField_injective ⊤)
  have : NeZero (q : Γ(Z, ⊤)) := ⟨(hqU ⊤).ne_zero⟩
  refine ⟨⟨s, hqU ⊤, ?_⟩⟩
  have hr := (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := s)).2 hps
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hr

end LateralTheory.E.RootPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpectrumLimits
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

def IsCop {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) : Prop :=
  ∀ (R : Type) [CommRing R] (g : ι → (A' →+* R)) (c : A →+* R), (∀ i, (g i).comp φ = c) →
    ∃! h : B →+* R, (∀ i, h.comp (l i) = g i) ∧ h.comp χ = c

theorem le_l {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B)
    (f : A' →+* B) (hf : f.comp φ = χ) (I : Ideal A) : I.map φ ≤ (I.map χ).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hf]

abbrev lq {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B)
    (f : A' →+* B) (hf : f.comp φ = χ) (I : Ideal A) : A' ⧸ I.map φ →+* B ⧸ I.map χ :=
  Ideal.quotientMap (I.map χ) f (le_l φ χ f hf I)

def coneOf {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) :
    Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : ι => yoneda.obj (Spec (CommRingCat.of A'))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom φ)))) :=
  WidePullbackShape.mkCone (yoneda.map (Spec.map (CommRingCat.ofHom χ))) (fun i => yoneda.map (Spec.map (CommRingCat.ofHom (l i))))
    (fun i => by
      change yoneda.map _ ≫ yoneda.map (Spec.map (CommRingCat.ofHom φ)) = _
      rw [← yoneda.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i])

def SpecLim : Prop := ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) (n : ℕ)
  (l : Fin (n + 1) → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ), IsCop φ χ l → Nonempty (IsLimit (coneOf φ χ l hl))

def TensCop : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (n : ℕ),
  ∃ (B : Type) (_ : CommRing B) (χ : A →+* B) (l : Fin (n + 1) → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ),
    Subring.closure (⋃ i, Set.range (l i)) = ⊤ ∧ IsCop φ χ l

def QuotCop : Prop := ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
  (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (I : Ideal A), IsCop φ χ l →
    IsCop (qm φ I) (qm χ I) (fun i => lq φ χ (l i) (hl i) I)

theorem lq_hl {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
  (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (I : Ideal A) (i : ι) :
    (lq φ χ (l i) (hl i) I).comp (qm φ I) = qm χ I := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp [qm, lq, ← hl i]

theorem ysq {R S S' T : Type} [CommRing R] [CommRing S] [CommRing S'] [CommRing T] (f : R →+* S) (g : S →+* T)
    (f' : R →+* S') (g' : S' →+* T) (h : g.comp f = g'.comp f') :
    yoneda.map (Spec.map (CommRingCat.ofHom g)) ≫ yoneda.map (Spec.map (CommRingCat.ofHom f)) =
      yoneda.map (Spec.map (CommRingCat.ofHom g')) ≫ yoneda.map (Spec.map (CommRingCat.ofHom f')) := by
  rw [← yoneda.map_comp, ← yoneda.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, h]

theorem LevelsGen_of (hT : TensCop) (hQ : QuotCop) (hS : SpecLim) : LevelsGen := by
  intro A A' _ _ φ I p
  obtain ⟨B, _, χ, l, hl, hc, hcop⟩ := hT A A' φ (p.unop.len)
  refine ⟨B, inferInstance, χ, _, l, hl, hc, ?_⟩
  obtain ⟨L⟩ := hS A A' B φ χ _ l hl hcop
  obtain ⟨Lr⟩ := hS _ _ _ (qm φ I) (qm χ I) _ _ (lq_hl φ χ l hl I) (hQ A A' B φ χ l hl I hcop)
  let e : (cech (Spec.map (CommRingCat.ofHom φ))).obj p ≅
      yoneda.obj (Spec (CommRingCat.of B)) := (limit.isLimit _).conePointUniqueUpToIso L
  let er : (cech (Spec.map (CommRingCat.ofHom (qm φ I)))).obj p ≅
      yoneda.obj (Spec (CommRingCat.of (B ⧸ I.map χ))) := (limit.isLimit _).conePointUniqueUpToIso Lr
  refine ⟨Arrow.isoMk er e ?_⟩
  simp only [Arrow.mk_hom]
  apply L.hom_ext
  rintro (_|i)
  · have h1 : er.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (qm χ I))) = (WidePullback.base _ : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp Lr none
    have h2 : e.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ)) = (WidePullback.base _ : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp L none
    change (er.hom ≫ _) ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ)) =
      ((psi φ I).app p ≫ e.hom) ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ))
    rw [Category.assoc, Category.assoc, h2, ysq χ (Ideal.Quotient.mk (I.map χ)) (Ideal.Quotient.mk I) (qm χ I) (qm_comp χ I).symm,
      ← Category.assoc, h1]
    simp only [psi, Arrow.mapCechNerve_app, sqA, Arrow.homMk_right]
    erw [WidePullback.lift_base]
    all_goals rfl
  · have h1 : er.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (lq φ χ (l i) (hl i) I))) = (WidePullback.π _ i : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp Lr (some i)
    have h2 : e.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i))) = (WidePullback.π _ i : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp L (some i)
    change (er.hom ≫ _) ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i))) =
      ((psi φ I).app p ≫ e.hom) ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i)))
    rw [Category.assoc, Category.assoc, h2, ysq (l i) (Ideal.Quotient.mk (I.map χ)) (Ideal.Quotient.mk (I.map φ))
      (lq φ χ (l i) (hl i) I) (Ideal.quotientMap_comp_mk _).symm, ← Category.assoc, h1]
    simp only [psi, Arrow.mapCechNerve_app, sqA, Arrow.homMk_left]
    erw [WidePullback.lift_π]
    all_goals rfl

end LateralTheory.E.LevelsGenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.StandardEtaleChartsMultivariableHensel


attribute [local instance] MvPolynomial.gradedAlgebra in
def stdOpen (i : Fin 2) : P1.Opens := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

def StdPair {A : Type} [CommRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z) : Prop :=
  ∃ (L : Scheme.{0}) (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P1), IsIntegralHom u ∧ IsProper l ∧
    IsPullback f l (terminal.from P1) (terminal.from _) ∧ u ≫ l = p ∧
    Set.range ι₁ = ((u ≫ f) ⁻¹ᵁ stdOpen 0 : Set Z) ∧ Set.range ι₂ = ((u ≫ f) ⁻¹ᵁ stdOpen 1 : Set Z)

def StdCharts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p →
  ∃ (U V : Scheme.{0}) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ ∧ IsOpenImmersion ι₂ ∧ IsAffine U ∧ IsAffine V ∧
    Set.range ι₁ ∪ Set.range ι₂ = Set.univ ∧ StdPair p ι₁ ι₂

def Heart : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  StdPair p ι₁ ι₂ →
  ∀ g : LocallyConstant ↥(pullback (fibMap p ι₁) (fibMap p ι₂)) (ZMod q),
    ∃ (a : LocallyConstant ↥(fib (ι₁ ≫ p)) (ZMod q)) (b : LocallyConstant ↥(fib (ι₂ ≫ p)) (ZMod q)),
      g = a.comap (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base.hom -
        b.comap (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base.hom

theorem chartSurj (hR : LateralTheory.E.ChartSurjCut.Root) (hL : LateralTheory.E.ChartSurjCut.LCIso) (hT : Heart) :
    ∀ (H : Hyp) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
    ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
    IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
    StdPair p ι₁ ι₂ →
    ∀ w : Ht q (sch.obj (pullback (fibMap p ι₁) (fibMap p ι₂))) 0 i, ∃ a b,
      w = pull _ (sch.map (pullback.fst (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 a -
        pull _ (sch.map (pullback.snd (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 b := by
  unfold LateralTheory.E.ChartSurjCut.Root at hR
  unfold LateralTheory.E.ChartSurjCut.LCIso at hL
  intro H q i A _ _ hSH hq Z U V p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd w
  obtain ⟨ζ⟩ := hR q A p hZ hq
  obtain ⟨e, he⟩ := hL H q i Z ζ
  have k1 : fibMap p ι₁ ≫ pullback.fst p (cpt A) = pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have k2 : fibMap p ι₂ ≫ pullback.fst p (cpt A) = pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have eq : pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ =
      pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by
    rw [← k2, ← k1, ← Category.assoc, ← pullback.condition, Category.assoc]
  obtain ⟨a, b, hab⟩ := hT q A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd
    ((e _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁)).symm w)
  refine ⟨e _ (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁) a, e _ (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂) b, ?_⟩
  rw [he _ _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂)) rfl, he _ _ (pullback.snd (fibMap p ι₁) (fibMap p ι₂)) eq,
    ← map_sub, ← hab, AddEquiv.apply_symm_apply]

theorem goal_of (hMV : MV) (hC : StdCharts) (hF : LateralTheory.E.LineOneCut.FibCover) (hA : ChartAcyc)
    (hR : LateralTheory.E.ChartSurjCut.Root) (hL : LateralTheory.E.ChartSurjCut.LCIso) (hT : Heart) : LineOne := by
  intro H q i A _ _ hSH hq Z p hp hZ
  obtain ⟨U, V, ι₁, ι₂, h1, h2, hU, hV, hcov, hstd⟩ := hC A p hp
  obtain ⟨hf1, hf2, hfcov⟩ := hF A p ι₁ ι₂ h1 h2 hcov
  obtain ⟨δ, hex, -⟩ := hMV H (ZMod q) (tw q i)
  have e := hex (fibMap p ι₁) (fibMap p ι₂) hfcov 0
  have aU := hA H q A p ι₁ h1 hU hZ hq
  have aV := hA H q A p ι₂ h2 hV hZ hq
  have key : ∀ x : Ht q (sch.obj (fib p)) 1 i, x = 0 := by
    intro x
    have s1 := aU 1 i one_pos
    have s2 := aV 1 i one_pos
    obtain ⟨w, hw⟩ := (e.2.2 x).1 ⟨@Subsingleton.elim _ s1 _ _, @Subsingleton.elim _ s2 _ _⟩
    obtain ⟨a, b, hab⟩ := chartSurj hR hL hT H q i A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd w
    rw [← hw]
    exact (e.2.1 w).2 ⟨a, b, hab⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end LateralTheory.E.StandardEtaleChartsMultivariableHensel
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StandardChartsLineZero
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StandardEtaleChartsIdempotentGluing

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def mS (S : Subalgebra A K) : Submodule A K := IsLocalRing.maximalIdeal A • Subalgebra.toSubmodule S

def AdjoinInv (B : Subalgebra A K) (t : K) : Subalgebra A K := Algebra.adjoin A ((B : Set K) ∪ {t⁻¹})

structure Charts (B C : Subalgebra A K) (t : K) : Prop where
  ne : t ≠ 0
  tB : t ∈ B
  tC : t⁻¹ ∈ C
  intB : ∀ b ∈ B, IsIntegral (Algebra.adjoin A {t}) b
  intC : ∀ c ∈ C, IsIntegral (Algebra.adjoin A {t⁻¹}) c
  glue : AdjoinInv B t = Algebra.adjoin A ((C : Set K) ∪ {t})

def IdemPair (B C : Subalgebra A K) (t e f : K) : Prop :=
  e ∈ B ∧ f ∈ C ∧ e * e - e ∈ mS B ∧ f * f - f ∈ mS C ∧ e - f ∈ mS (AdjoinInv B t)

def StdCharts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

def IdemLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f →
  ∃ g ∈ B, g ∈ C ∧ g - e ∈ mS B ∧ g - f ∈ mS C

def AlgGlue : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → (∀ x ∈ B, x ∈ C → IsIntegral A x) → ∀ e f : K, IdemPair B C t e f →
  (e ∈ mS B ∧ f ∈ mS C) ∨ (e - 1 ∈ mS B ∧ f - 1 ∈ mS C)

theorem goal_of (hS : StdCharts) (hG : AlgGlue) : LateralTheory.E.t_E2Cut.LineZero := by
  intro A _ _ hSH Z p hIL hZ
  obtain ⟨hH, -⟩ := hSH
  have hne : Nonempty ↑(pullback p (cpt A)) := by
    obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
    have := hl.1
    have := hZ.1
    exact LateralTheory.E.LineZeroCut.lzNonempty A (u ≫ l) inferInstance inferInstance
  obtain ⟨K, _, _, B, C, t, hc, hint, hW⟩ := hS A p hIL hZ
  have hpre : PreconnectedSpace ↑(pullback p (cpt A)) := by
    rw [preconnectedSpace_iff_clopen]
    intro W hW'
    obtain ⟨e, f, hef, h0, h1⟩ := hW W hW'
    rcases hG A K B C t hc hint e f hef with h | h
    · exact Or.inl (h0 h)
    · exact Or.inr (h1 h)
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

end LateralTheory.E.StandardEtaleChartsIdempotentGluing
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.SHLocPf

namespace LateralTheory.E.ColimPf

def Absorb : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (ψ : O →+* Ω), IE f ∧ ψ.comp f.hom = ι ∧
    (∀ x : O, ψ x ≠ 0 → IsUnit x) ∧
    ∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φ : B →+* Ω, φ.comp g.hom = ι →
      ∃ h : B ⟶ O, g ≫ h = f ∧ ψ.comp h.hom = φ

def Rigid : Prop := ∀ (A B O : CommRingCat.{0}) (Ω : Type) [Field Ω] (ψ : O →+* Ω) (g : A ⟶ B), Et g →
  (∀ x : O, ψ x ≠ 0 → IsUnit x) → ∀ (u v : B ⟶ O), g ≫ u = g ≫ v → ψ.comp u.hom = ψ.comp v.hom → u = v

def Descend : Prop := ∀ (A O : CommRingCat.{0}) (f : A ⟶ O), IE f →
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C],
  ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (d : B ⟶ O) (C' : CommRingCat.{0}) (e : B ⟶ C') (c : C' →+* C),
    Et g ∧ Et e ∧ g ≫ d = f ∧ c.comp e.hom = (algebraMap O C).comp d.hom ∧
    (∀ k : C' ⟶ O, e ≫ k = d → ∃ s : C →ₐ[O] O, s.toRingHom.comp c = k.hom) ∧
    (∀ (R : Type) [CommRing R] (α β : C →+* R), α.comp (algebraMap O C) = β.comp (algebraMap O C) →
      α.comp c = β.comp c → α = β)

theorem et_comp {A B C : CommRingCat.{0}} {g : A ⟶ B} {e : B ⟶ C} (hg : Et g) (he : Et e) : Et (g ≫ e) := by
  change (g ≫ e).hom.Etale
  rw [CommRingCat.hom_comp]
  exact RingHom.Etale.stableUnderComposition _ _ hg he

theorem Colim_of (hA : Absorb) (hR : Rigid) (hD : Descend) : Colim := by
  intro A Ω _ ι
  obtain ⟨O, f, ψ, hIE, hcomp, hloc, habs⟩ := hA A Ω ι
  refine ⟨O, f, ψ, hIE, hcomp, ?_⟩
  intro C _ _ _ χ hχ
  obtain ⟨B, g, d, C', e, c, hg, he, hgd, hce, hext, hgen⟩ := hD A O f hIE C
  have ce : ∀ y, c (e.hom y) = algebraMap O C (d.hom y) := fun y => DFunLike.congr_fun hce y
  have cχ : ∀ z, χ (algebraMap O C z) = ψ z := fun z => DFunLike.congr_fun hχ z
  have gd : ∀ x, d.hom (g.hom x) = f.hom x := fun x => by rw [← hgd]; rfl
  have hpt : (χ.comp c).comp (g ≫ e).hom = ι := by
    ext x
    simp only [RingHom.comp_apply, CommRingCat.hom_comp]
    rw [ce, cχ, gd, ← hcomp]; rfl
  obtain ⟨h, hh1, hh2⟩ := habs C' (g ≫ e) (et_comp hg he) (χ.comp c) hpt
  have hed : e ≫ h = d := by
    refine hR A B O Ω ψ g hg hloc (e ≫ h) d ?_ ?_
    · rw [← Category.assoc, hh1, hgd]
    · ext y
      have := DFunLike.congr_fun hh2 (e.hom y)
      simp only [RingHom.comp_apply, CommRingCat.hom_comp] at this ⊢
      rw [this, ce, cχ]
  obtain ⟨s, hs⟩ := hext h hed
  refine ⟨s, hgen Ω _ _ ?_ ?_⟩
  · ext x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rw [cχ]; rfl
  · ext y
    have h1 := DFunLike.congr_fun hs y
    have h2 := DFunLike.congr_fun hh2 y
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]

end LateralTheory.E.ColimPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TruncationPieces
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf

namespace LateralTheory.E.TruncationPieces

def RelK (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (HK.pull R f F m)) ∧ Function.Injective (HK.pull R f F n)

def piece (R : Type) [CommRing R] {U E : Spc} (u : U ⟶ E) (p : ℕ) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (((chains R).obj U).X (-(p : ℤ))) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (((chains R).obj E).X (-(p : ℤ))) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (((chains R).map u).f (-(p : ℤ)))

def Piece : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (p : ℕ) (k : ℤ),
  RelZS R F k (disc.map (u.app (Opposite.op (SimplexCategory.mk p)))) → RelK R F (k + p) (piece R u p)

def Filt : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (n : ℤ),
  (∀ p : ℕ, RelK R F n (piece R u p)) → RelZS R F n u

theorem etale_relK_single_degree_pieces_of_piece_and_filtration (hP : Piece) (hF : Filt) : LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels := by
  intro R _ F U E u n hlow h0
  refine hF R F u n (fun p => ?_)
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have := hP R F u 0 n h0
    simpa using this
  · have hk : n - (p : ℤ) < n := by omega
    have := hP R F u p (n - p) (hlow p (n - p) hk)
    simpa using this

end LateralTheory.E.TruncationPieces
end
end

