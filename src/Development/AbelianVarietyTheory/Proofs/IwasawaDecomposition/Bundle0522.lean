module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0510
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisOfIntFrame
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM
open GlobalTheory.GradedPieces GlobalTheory.Points

namespace GlobalTheory.TotalFrame

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_basis_sigma {O S M J : Type} [CommRing O] [CommRing S] [AddCommGroup M] [Module S M] [Fintype J]
    {χ : J → O →+* S} (h : EigenSplit.IsSplitting χ) (ρ : O →+* Module.End S M) {m : J → ℕ}
    (u : ∀ σ, Fin (m σ) → M) (li : ∀ σ, LinearIndependent S (u σ))
    (hs : ∀ σ, Submodule.span S (Set.range (u σ)) = EigenSplit.eigenSub ρ (χ σ)) :
    ∃ b : Module.Basis (Σ σ, Fin (m σ)) S M, ∀ σ a, b ⟨σ, a⟩ = u σ a := by
  classical
  have hi := EigenSplit.isInternal_eigenSub h ρ
  simp only [← hs] at hi
  exact ⟨hi.collectedBasis fun σ => Module.Basis.span (li σ), fun σ a => by
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact congrArg Subtype.val (Module.Basis.span_apply (li σ) a)⟩

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {m : ℕ}

theorem exists_basis {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w) :
    ∃ b : Module.Basis (Fin m) S (TanM x t.G), ∀ i, b i = tanOf (hv i) := by
  refine ⟨Module.Basis.mk (v := fun i => tanOf (hv i)) (Fintype.linearIndependent_iffₛ.2 fun c c' h => congrFun
    ((hb _ (isTan_tv (∑ i, c i • tanOf (hv i)))).unique ((isComb_iff (fun i => tanOf (hv i)) c _).2 rfl)
      ((isComb_iff (fun i => tanOf (hv i)) c' _).2 h))) fun w _ => ?_, fun i => Module.Basis.mk_apply _ _ i⟩
  obtain ⟨a, ha, -⟩ := hb _ (isTan_tv w)
  rw [(isComb_iff (fun i => tanOf (hv i)) a w).1 ha]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_basis_map {J : Type} [Fintype J] (b : Module.Basis J S (TanM x t.G)) (φ : S →+* T) {x' : Sp T ⟶ X}
    (hx : spMap φ ≫ x = x') :
    ∃ b' : Module.Basis J T (TanM x' t.G), ∀ i, (tv (b' i)).left = spMap (dualMap φ) ≫ (tv (b i)).left := by
  let e := Fintype.equivFin J
  have hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x (fun i => (tv (b.reindex e i)).left) cf w := fun w hw =>
    ⟨(b.reindex e).repr (tanOf hw), (isComb_iff _ _ (tanOf hw)).2 ((b.reindex e).sum_repr _).symm, fun a ha => by
      rw [(isComb_iff _ _ (tanOf hw)).1 ha, Module.Basis.repr_sum_self]⟩
  obtain ⟨b', hb'⟩ := exists_basis (fun i => isTan_map φ hx (isTan_tv (b.reindex e i)))
    (basis_map φ hx (fun i => isTan_tv _) hb)
  refine ⟨b'.reindex e.symm, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hb', left_tanOf, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem dualMap_epsMul (φ : S →+* T) (a : S) {Y : Scheme.{0}} (v : Sp (DualNumber S) ⟶ Y) :
    spMap (dualMap φ) ≫ spMap (epsMul a) ≫ v = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) ≫ v := by
  rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap]
  congr 2
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

variable {Dw : Datum H} {l : Level H} {c : Coeff l} {w : Vecs Dw t S} {χ : (E →+* ℂ) → 𝓞 E →+* S}


variable (c x w χ) in
def FramesSeparate : Prop :=
  ∀ r s : S, (∀ (k : Type) [Field k] (φ : S →+* k) (f : c.F →+* k), IsFrame t f (spMap φ ≫ x) (w.bc φ) →
    (∀ σ a, f (embK c σ a) = φ (χ σ a)) → φ r = φ s) → r = s

theorem span_eq_eigenSub (hw : FramesSeparate x c w χ) (σ : E →+* ℂ) (ht : ∀ i, IsTanAtG t x (w σ i))
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (e : Fin (Dw.mult σ) ↪ Fin m) (he : ∀ i, v (e i) = w σ i)
    (hv : ∀ i, IsTanAtG t x (v i)) (hb : ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u) :
    Submodule.span S (Set.range fun i => tanOf (ht i)) = EigenSplit.eigenSub (actR t.act) (χ σ) := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun u hu => ?_
  · rintro _ ⟨i, rfl⟩
    refine EigenSplit.mem_eigenSub.2 fun a => ?_
    obtain ⟨g, hc, -⟩ := hb _ (isTan_tv (actR t.act a (tanOf (ht i))))
    obtain ⟨g', hc', -⟩ := hb _ (isTan_tv (χ σ a • tanOf (ht i)))
    have hcc : g = g' := funext fun l => hw _ _ fun k _ φ f hf hfj => by
      have h1 := comb_map φ rfl hc
      have h2 := comb_map φ rfl hc'
      have h3 : spMap (dualMap φ) ≫ (tv (actR t.act a (tanOf (ht i)))).left =
          spMap (dualMap φ) ≫ (tv (χ σ a • tanOf (ht i))).left := by
        refine (Category.assoc _ _ _).symm.trans (((hf.1 σ i).2 a).trans ?_)
        rw [hfj]
        exact (dualMap_epsMul φ _ _).symm
      rw [h3] at h1
      exact congrFun ((basis_map φ rfl hv hb _ (isTan_map φ rfl (isTan_tv _))).unique h1 h2) l
    subst hcc
    exact ((isComb_iff (fun i => tanOf (hv i)) g _).1 hc).trans ((isComb_iff (fun i => tanOf (hv i)) g _).1 hc').symm
  · obtain ⟨g, hc, -⟩ := hb _ (isTan_tv u)
    rw [(isComb_iff (fun i => tanOf (hv i)) g _).1 hc]
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : ∃ i, e i = l
    · obtain ⟨i, rfl⟩ := hl
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, tan_ext (he i).symm⟩)
    have h0 : g l = 0 := hw _ _ fun k _ φ f hf hfj => by
      have hvk := fun i => isTan_map φ rfl (hv i)
      have huk := isTan_map φ rfl (isTan_tv u)
      obtain ⟨d, hd, -⟩ := hf.2 σ _ huk fun a => by
        rw [hfj, ← dualMap_epsMul, Category.assoc]
        exact congrArg (fun q => spMap (dualMap φ) ≫ (tv q).left) (EigenSplit.mem_eigenSub.1 hu a)
      have h1 := (comb_iff hvk _ huk).1 (comb_map φ rfl hc)
      have h2 := (comb_iff (fun i => (hf.1 σ i).1) _ huk).1 hd
      have h3 : ∑ i, d i • tanOf (hf.1 σ i).1 = ∑ l, Function.extend e d 0 l • tanOf (hvk l) :=
        Fintype.sum_of_injective e e.injective _ _
          (fun l hl => by rw [Function.extend_apply' _ _ _ hl, Pi.zero_apply, zero_smul])
          (fun i => by
            rw [e.injective.extend_apply]
            exact congrArg (d i • ·) (tan_ext (congrArg (spMap (dualMap φ) ≫ ·) (he i).symm)))
      rw [map_zero, Fintype.linearIndependent_iffₛ.1 (linInd_of_basis hvk (basis_map φ rfl hv hb)) _ _
        (h1.symm.trans (h2.trans h3)) l, Function.extend_apply' _ _ _ hl, Pi.zero_apply]
    rw [h0, zero_smul]
    exact Submodule.zero_mem _

theorem exists_basis_total (hw : FramesSeparate x c w χ) (hχ : EigenSplit.IsSplitting χ)
    (h : ∀ σ, ∃ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n),
      (∀ i, v (e i) = w σ i) ∧ (∀ i, IsTanAtG t x (v i)) ∧ ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u)
    (φ : S →+* T) {x' : Sp T ⟶ X} (hx : spMap φ ≫ x = x') :
    ∃ b : Module.Basis (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) T (TanM x' t.G), ∀ σ a, (tv (b ⟨σ, a⟩)).left = w.bc φ σ a := by
  choose n v e he hv hb using h
  have ht : ∀ σ i, IsTanAtG t x (w σ i) := fun σ i => he σ i ▸ hv σ (e σ i)
  have li : ∀ σ, LinearIndependent S fun i => tanOf (ht σ i) := fun σ => by
    obtain ⟨b, hb'⟩ := exists_basis (hv σ) (hb σ)
    convert b.linearIndependent.comp (e σ) (e σ).injective using 1
    exact funext fun i => Eq.trans (tan_ext (w := tanOf (hv σ (e σ i))) (he σ i).symm) (hb' (e σ i)).symm
  obtain ⟨b, hb'⟩ := exists_basis_sigma hχ _ (fun σ i => tanOf (ht σ i)) li
    fun σ => span_eq_eigenSub hw σ (ht σ) (e σ) (he σ) (hv σ) (hb σ)
  obtain ⟨b', hb''⟩ := exists_basis_map b φ hx
  exact ⟨b', fun σ a => by rw [hb'', hb']; rfl⟩

end Tangent

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def embV {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c σ).codRestrict (c.V W) fun a =>
    GlobalTheory.CoeffRings.mem_of_isIntegral _ (map_isIntegral_int (embK c σ) (RingOfIntegers.isIntegral a))

theorem isSplitting_embV {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (hd : ¬ p ∣ (discr E).natAbs) {S : Type} [CommRing S] (j : c.V W →+* S) :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => j.comp (embV c W σ) := by
  refine EigenSplit.isSplitting_of_isDomain (fun σ τ h => ?_) (NumberField.Embeddings.card E ℂ) j ?_
  · exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      (RingHom.ext fun a => congrArg (fun f : 𝓞 E →+* c.V W => (((f a : c.V W) : c.F) : ℂ)) h)
  · have hu := (((GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).2.2.2 p W hp hW).2.1 _
      (hp.coprime_iff_not_dvd.2 hd).symm).map j
    rw [map_natCast] at hu
    rcases Int.natAbs_eq (discr E) with h | h <;> rw [h]
    · rwa [Int.cast_natCast]
    · rw [Int.cast_neg, Int.cast_natCast]
      exact hu.neg

variable {Z : Mdl Y i₀} {U : Z.X.Opens} {hU : IsAffineOpen U} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)}


variable (hU) in
theorem fn_ext_affine {f g : Γ(Z.X, U)} (h : ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k),
    Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn → φ f = φ g) : f = g :=
  fn_ext Z fun k _ x hx ho => by
    rw [valR_eq x U hx, valR_eq x U hx]
    exact h k (valMap x U hx).hom (by
      rw [show spMap (valMap x U hx).hom ≫ hU.fromSpec = x from specMap_valMap_fromSpec hU x hx]
      exact ho)

theorem frame_at (hw : IntFrame Z hU w) {j : Z.i.c.V W →+* Γ(Z.X, U)} (hj : spMap j = hU.fromSpec ≫ Z.s)
    {k : Type} [Field k] (φ : Γ(Z.X, U) →+* k) (ho : Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn) :
    ∃ f : Z.i.c.F →+* k, IsFrame (Y Z.i).t f (spMap φ ≫ hU.fromSpec ≫ Z.π) (w.bc φ) ∧
      ∀ σ a, f (embK Z.i.c σ a) = φ (j (embV Z.i.c W σ a)) := by
  obtain ⟨a, ψ, hx, hf, -⟩ := hw.2 k φ ho
  rw [Category.assoc] at hf
  refine ⟨_, hf, fun σ r => ?_⟩
  have e : spMap (ψ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) = spMap (φ.comp j) := by
    rw [← spMap_comp_spMap _ ψ, ← spMap_comp_spMap _ φ, hj, ← Z.alg_s a, ← Category.assoc, hx, Category.assoc]
  exact congrArg (fun q => q.hom (embV Z.i.c W σ r)) (Spec.map_injective e)

end Model

theorem exists_basis_of_intFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ¬ p ∣ (discr E).natAbs →
    ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U)
      (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (R : Type) [CommRing R] (φ : Γ(Z.X, U) →+* R)
      (x : Sp R ⟶ Z.X), spMap φ ≫ hU.fromSpec = x →
      ∃ b : Module.Basis (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) R (TanM (x ≫ Z.π) (Y Z.i).t.G),
        ∀ σ a, (tv (b ⟨σ, a⟩)).left = w.bc φ σ a := by
  intro E _ _ _ H Dw Xo p W hp hW hd Y i₀ Z U hU w hw R _ φ x hx
  let j : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.s)).hom
  have hj : spMap j = hU.fromSpec ≫ Z.s := Spec.map_preimage _
  refine exists_basis_total (c := Z.i.c) (fun r s h => fn_ext_affine hU fun k _ ψ ho => ?_)
    (isSplitting_embV Z.i.c hp hW hd j) hw.1 φ (hx ▸ (Category.assoc _ _ _).symm)
  obtain ⟨f, hf, hfj⟩ := frame_at hw hj ψ ho
  exact h k ψ f hf hfj

end GlobalTheory.TotalFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSections
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.AnForm.R

namespace GlobalTheory.ProjBlowup

theorem exists_blowup_graph {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (hσ : Generates J σ) :
    ∃ (G : Scheme.{0}) (b : G ⟶ X) (c : G ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      FinalTheorems.Blowup b J ∧ Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  have : IsProper (PSpace.str R m) := isProper_str R m
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let U : X.Opens := J.support.compl
  have hU : ∀ x : U.toScheme, U.ι x ∉ J.support := fun x => x.2
  have htop : ∀ {W : Scheme.{0}} (g : W ⟶ X), (∀ w, g w ∉ J.support) → J.comap g = ⊤ := fun g hg =>
    eq_top_of_forall_notMem _ fun w hw => hg w ((mem_support_comap J g w).1 hw)
  obtain ⟨φ, hφ, hφσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X U _ L m σ U.ι (U.ι ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ U.ι hσ)
    (by rw [htop _ hU]; exact effCartier_top _)
  let b := graphClosure.fst s (PSpace.str R m) U.ι φ hφ.symm
  let c := graphClosure.snd s (PSpace.str R m) U.ι φ hφ.symm
  let j := graphClosure.incl s (PSpace.str R m) U.ι φ hφ.symm
  have hjb : j ≫ b = U.ι := graphClosure.incl_fst ..
  have hjc : j ≫ c = φ := graphClosure.incl_snd ..
  have hbc : Proportional σ b c := .of_comp j (by rwa [hjb, hjc])
  have hc : b ≫ s = c ≫ PSpace.str R m := graphClosure.condition ..
  have hι : pullback.lift b c hc = graphClosure.ι s (PSpace.str R m) U.ι φ hφ.symm := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]; rfl
    · rw [pullback.lift_snd]; rfl
  refine ⟨_, b, c, hc, ⟨GlobalTheory.T.effCartier_of_proportional_sections R X _ U _ L m σ b c j (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ b hσ) hbc inferInstance
    inferInstance fun t => ?_, fun W g hg => ?_⟩, hbc, ?_⟩
  · rw [mem_support_comap, ← Scheme.Hom.comp_apply, hjb]; exact hU t
  · obtain ⟨ψ, hψ, hψσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X W _ L m σ g (g ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ g hσ) hg
    have hd := GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier W _ hg
    let d := Scheme.Opens.ι (X := W) (J.comap g).support.compl
    have hdU : ∀ t, (d ≫ g) t ∉ J.support := fun t ht => t.2 ((mem_support_comap J g _).2 ht)
    let w := IsOpenImmersion.lift U.ι (d ≫ g) (by
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨_, hdU t⟩, rfl⟩)
    have hw : w ≫ U.ι = d ≫ g := IsOpenImmersion.lift_fac ..
    have hw' : d ≫ ψ = w ≫ φ := _root_.GlobalTheory.ProjBlowup.eq_of_proportional R X _ L m σ (d ≫ g) _ _ (htop _ hdU ▸ GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ (d ≫ g) hσ)
      (by rw [Category.assoc, hψ, Category.assoc, hφ, reassoc_of% hw]) (hψσ.comp d) (hw ▸ hφσ.comp w)
    have key : ∀ h : W ⟶ _, h ≫ b = g → d ≫ h = w ≫ j := fun h hh => by
      have H := graphClosure.isPullback_incl s (PSpace.str R m) U.ι φ hφ.symm
      have e : w ≫ U.ι = (d ≫ h) ≫ b := by rw [hw, Category.assoc, hh]
      have h1 := H.lift_fst w (d ≫ h) e
      rw [Category.comp_id] at h1
      rw [← H.lift_snd w (d ≫ h) e, h1]
    have hl := graphClosure.lift_fst s (PSpace.str R m) U.ι φ hφ.symm g ψ hψ.symm d w hw.symm hw'
    exact ⟨_, hl, fun h hh => hom_ext_of_isSchemeTheoreticallyDominant d b ((key h hh).trans (key _ hl).symm)
      (hh.trans hl.symm)⟩
  · rw [hι]; infer_instance

theorem exists_iso_of_blowup {X X' G : Scheme.{0}} (J : X.IdealSheafData) (b : X' ⟶ X) (b₀ : G ⟶ X)
    (hb : FinalTheorems.Blowup b J) (hb₀ : FinalTheorems.Blowup b₀ J) : ∃ e : X' ⟶ G, IsIso e ∧ e ≫ b₀ = b := by
  obtain ⟨e, he, -⟩ := hb₀.2 X' b hb.1
  obtain ⟨e', he', -⟩ := hb.2 G b₀ hb₀.1
  have h1 : e ≫ e' = 𝟙 X' := by
    obtain ⟨_, -, hu⟩ := hb.2 X' b hb.1
    rw [hu (e ≫ e') (by show (e ≫ e') ≫ b = b; rw [Category.assoc, he', he]), hu (𝟙 X') (Category.id_comp _)]
  have h2 : e' ≫ e = 𝟙 G := by
    obtain ⟨_, -, hu⟩ := hb₀.2 G b₀ hb₀.1
    rw [hu (e' ≫ e) (by show (e' ≫ e) ≫ b₀ = b₀; rw [Category.assoc, he, he']), hu (𝟙 G) (Category.id_comp _)]
  exact ⟨e, ⟨e', h1, h2⟩, he⟩

theorem exists_closedImmersion_of_generates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X X' : Scheme.{0})
    (s : X ⟶ Sp R) (J : X.IdealSheafData)
    (b : X' ⟶ X) (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), IsProjOver s → FinalTheorems.Blowup b J →
    GlobalTheory.ProjBlowup.Generates J σ → ∃ (c : X' ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      GlobalTheory.ProjBlowup.Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  intro R _ _ X X' s J b L₀ m σ hs hb hσ
  obtain ⟨G, b₀, c₀, hc₀, hb₀, hp₀, hi₀⟩ := exists_blowup_graph s hs J L₀ m σ hσ
  obtain ⟨e, he, heb⟩ := exists_iso_of_blowup J b b₀ hb hb₀
  have hc : b ≫ s = (e ≫ c₀) ≫ PSpace.str R m := by rw [← heb, Category.assoc, Category.assoc, hc₀]
  have hp : Proportional σ b (e ≫ c₀) := heb ▸ hp₀.comp e
  have hl : pullback.lift b (e ≫ c₀) hc = e ≫ pullback.lift b₀ c₀ hc₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, heb]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  refine ⟨e ≫ c₀, hc, hp, ?_⟩
  rw [hl]
  infer_instance

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompactRepresentativesModTorusPoints
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.BdArc
  Filter Topology
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan GlobalTheory.Points GlobalTheory.IntegralPower

namespace GlobalTheory.TorusCocompact

theorem exists_isCompact_surjOn {V H : Type} [NormedAddCommGroup V] [ProperSpace V] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [T2Space H] (φ : V → H) (hφ : ∀ z w, φ (z + w) = φ z * φ w)
    (hs : Function.Surjective φ) (hc : Continuous φ) : ∃ C : Set V, IsCompact C ∧ ∀ z, ∃ c ∈ C, φ (z - c) = 1 := by
  let ψ : V →+ Additive H := AddMonoidHom.mk' (fun z => Additive.ofMul (φ z)) hφ
  have : BaireSpace (Additive H) := inferInstanceAs (BaireSpace H)
  have : T2Space (Additive H) := inferInstanceAs (T2Space H)
  have ho : IsOpenMap φ := AddMonoidHom.isOpenMap_of_sigmaCompact ψ hs hc
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover (fun n : ℕ => φ '' Metric.ball 0 n)
    (fun n => ho _ Metric.isOpen_ball) (fun h _ => by
      obtain ⟨z, rfl⟩ := hs h
      obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
      exact Set.mem_iUnion.2 ⟨n, z, by simpa using hn, rfl⟩)
    (Monotone.directed_le fun m n h => Set.image_mono (Metric.ball_subset_ball (Nat.cast_le.2 h)))
  refine ⟨Metric.closedBall 0 n, isCompact_closedBall _ _, fun z => ?_⟩
  obtain ⟨c, hc, hcz⟩ := hn (Set.mem_univ (φ z))
  refine ⟨c, Metric.ball_subset_closedBall hc, ?_⟩
  have h := hφ (z - c) c
  rw [sub_add_cancel, hcz] at h
  exact (mul_eq_right.1 h.symm)

theorem exists_lift_point {A B : Over (Sp ℂ)} (q : A ⟶ B) [Surjective q.left] [LocallyOfFiniteType q.left]
    (w : Over.mk (𝟙 (Sp ℂ)) ⟶ B) : ∃ u : Over.mk (𝟙 (Sp ℂ)) ⟶ A, u ≫ q = w := by
  let w' : Sp ℂ ⟶ B.left := w.left
  obtain ⟨z, -⟩ := (pullback.snd q.left w').surjective (IsLocalRing.closedPoint ℂ)
  obtain ⟨x, hx, -⟩ := GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd q.left w') isClosed_univ.isLocallyClosed
    ⟨z, trivial⟩
  have h : (x ≫ pullback.fst q.left w') ≫ q.left = w' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  refine ⟨Over.homMk (x ≫ pullback.fst q.left w') ?_, Over.OverMorphism.ext h⟩
  rw [← Over.w q, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h).trans (Over.w w)

section Fibre

variable {X : Scheme.{0}} {G : Over X} {y : Sp ℂ ⟶ X}

def fibrePt (x : Over.mk y ⟶ G) : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G :=
  Over.homMk (pullback.lift x.left (𝟙 (Sp ℂ)) ((Over.w x).trans (Category.id_comp y).symm))
    (pullback.lift_snd _ _ _)

theorem fibrePt_fst (x : Over.mk y ⟶ G) : (fibrePt x).left ≫ pullback.fst G.hom y = x.left :=
  pullback.lift_fst _ _ _

theorem fibre_ext {u v : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G}
    (h : u.left ≫ pullback.fst G.hom y = v.left ≫ pullback.fst G.hom y) : u = v :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w u).trans (Over.w v).symm))

theorem fibrePt_surjective : Function.Surjective (fibrePt (G := G) (y := y)) := fun u =>
  ⟨Over.homMk (u.left ≫ pullback.fst G.hom y) (by
    have h : u.left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w u
    rw [Category.assoc, pullback.condition, reassoc_of% h]
    rfl), fibre_ext (fibrePt_fst _)⟩

theorem fibrePt_mul [GrpObj G] (a b : Over.mk y ⟶ G) : fibrePt (a * b) = fibrePt a * fibrePt b := by
  let U : Over.mk ((Over.mk (𝟙 (Sp ℂ))).hom ≫ y) ⟶ Over.mk y := Over.homMk (𝟙 (Sp ℂ)) rfl
  have hU : ∀ x : Over.mk y ⟶ G, (U ≫ x).left = x.left := fun x => Category.id_comp _
  refine fibre_ext ?_
  rw [fibrePt_fst, ← (isGrpPullback_pullback G y).2 _ (fibrePt a) (fibrePt b) (U ≫ a) (U ≫ b)
    ((hU a).trans (fibrePt_fst a).symm) ((hU b).trans (fibrePt_fst b).symm), ← comp_mul, hU]

theorem continuous_fibrePt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (e : V → (Over.mk y ⟶ G))
    (he : IsHolTo Set.univ (fun z => (e z).left)) :
    Continuous fun z => leftPt (𝟙 (Sp ℂ)) (fibrePt (e z)) := by
  have h1 : Continuous fun z => leftPt y (e z) := by
    refine GlobalTheory.Points.continuous_iff.2 fun U => ⟨?_, fun f => ?_⟩
    · simpa using (he U 0).1
    · exact (he U f).2.continuousOn.mono fun _ hb => ⟨trivial, hb⟩
  refine (isEmbedding_of_isPullback (C := ℂ) (IsPullback.of_hasPullback G.hom y)).continuous_iff.2 ?_
  refine (h1.prodMk (continuous_const (y := 𝟙 (Sp ℂ)))).congr fun z => ?_
  exact Prod.ext (fibrePt_fst (e z)).symm (Over.w (fibrePt (e z))).symm

end Fibre


attribute [local instance] ptTopology in
theorem exists_isCompact_mod_torusPts : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (E : TorusExtension ((Over.pullback y).obj G)), IsSemiAbelian G →
    (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (e z).left) →
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) →
    ∃ C : Set (Fin g → ℂ), IsCompact C ∧ ∀ z, ∃ c ∈ C, e (z - c) ∈ torusPts G y E := by
  intro X G _ y g e E hG hadd hsurj hhol _
  let := E.addCommGroup
  let := E.grpB
  have := E.q_hom
  have := E.q_surjective
  have := E.isAbelian.proper
  have := hG.smooth
  have : LocallyOfFiniteType (E.q.left ≫ E.B.hom) := by
    rw [Over.w E.q]
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom y))
  have : LocallyOfFiniteType E.q.left := locallyOfFiniteType_of_comp _ E.B.hom
  have : CompactSpace (PtsOver E.B.hom (𝟙 (Sp ℂ))) := GlobalTheory.ProperPoints.compactSpace_pts E.B.hom
  have := compactSpace_of_ptsOver (𝟙 (Sp ℂ)) E.B
  have : IsTopologicalGroup (Over.mk (𝟙 (Sp ℂ)) ⟶ E.B) := by
    exact { continuous_mul := (continuous_comp_over _ (μ[E.B])).comp (continuous_lift _ E.B E.B)
            continuous_inv := continuous_comp_over _ (GrpObj.inv (X := E.B)) }
  have : T2Space (Over.mk (𝟙 (Sp ℂ)) ⟶ E.B) :=
    have := PtsOver.t2Space E.B.hom (𝟙 (Sp ℂ))
    T2Space.of_injective_continuous (f := fun x => (⟨x.left, Over.w x⟩ : PtsOver E.B.hom (𝟙 (Sp ℂ))))
      (fun _ _ h => Over.OverMorphism.ext (congrArg Subtype.val h))
      ((isEmbedding_leftPt (𝟙 (Sp ℂ)) E.B).continuous.subtype_mk _)
  obtain ⟨C, hC, H⟩ := exists_isCompact_surjOn (fun z => fibrePt (e z) ≫ E.q)
    (fun z w => by rw [hadd, fibrePt_mul, mul_comp])
    (fun w => by
      obtain ⟨u, rfl⟩ := exists_lift_point E.q w
      obtain ⟨x, rfl⟩ := fibrePt_surjective u
      obtain ⟨z, rfl⟩ := hsurj x
      exact ⟨z, rfl⟩)
    ((continuous_comp_over _ E.q).comp ((isEmbedding_leftPt _ _).continuous_iff.2 (continuous_fibrePt e hhol)))
  refine ⟨C, hC, fun z => ?_⟩
  obtain ⟨c, hc, hz⟩ := H z
  refine ⟨c, hc, E.isKernel.lift (fibrePt (e (z - c))) (toUnit _) hz, ?_⟩
  rw [IsPullback.lift_fst]
  exact fibrePt_fst _

end GlobalTheory.TorusCocompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeImports
section
set_option autoImplicit false

noncomputable section

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePairGram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def ent (M : Matrix (Fin r) (Fin r) ℂ) (a b : ℕ) : ℂ := if h : a < r ∧ b < r then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0


open Classical in
def coef (X : Data E r) (x x' : Frame X.Ψ r) (ρ : E →+* ℂ) (b i : ℕ) : ℂ :=
  if h : ρ ∈ X.Ψ then ent ((mat x' ⟨ρ, h⟩)⁻¹ * mat x ⟨ρ, h⟩) (X.p0 + b) (X.p0 + i)
  else if h' : conjEmb ρ ∈ X.Ψ then ent ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) (X.p0 - 1 - i) (X.p0 - 1 - b)
  else 0

end GlobalTheory.FramePairGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x), IsLocalRing R → f.Stable := by
  first | exact @GlobalTheory.ShFam.EigStable.stable_of_isLocalRing | exact GlobalTheory.ShFam.EigStable.stable_of_isLocalRing | (intros; apply GlobalTheory.ShFam.EigStable.stable_of_isLocalRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaximumPrincipleIsotropicFlowRescaledBoundStatement
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximum_principle_isotropicFlow_rescaledBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (w : ℝ), X.IsSec la P → FreqNonneg X la P → (∀ τ, X.spread la τ / 2 ≤ w) → StepBound X w (X.pnorm la P) := by
  first | exact @GlobalTheory.CuspStep.stepBound | exact GlobalTheory.CuspStep.stepBound | (intros; apply GlobalTheory.CuspStep.stepBound <;> assumption)
end

