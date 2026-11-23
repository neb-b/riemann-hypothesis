module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompData
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def exZ (Dw : Datum H) (G : WTZ E) : Ix Dw → ℤ
  | none => G.2
  | some x => G.1 (x.1, x.2)

theorem exZ_add (G G' : WTZ E) (i : Ix Dw) : exZ Dw (G + G') i = exZ Dw G i + exZ Dw G' i := by
  cases i <;> rfl

def frW (δ : Ix Dw → ℤ) (G : WTZ E) : ℤ := ∑ i, exZ Dw G i * δ i

theorem frW_add (δ : Ix Dw → ℤ) (G G' : WTZ E) : frW δ (G + G') = frW δ G + frW δ G' := by
  simp only [frW, exZ_add, add_mul, Finset.sum_add_distrib]

variable {Z : Comp Xo c}

def ordC (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (G : WTZ E) (x : AC Z) : ℤ :=
  WithTop.untopD 0 (v (x.coeff G)) + frW δ G

theorem ordC_single (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (G : WTZ E) {r : Om Z} (hr : r ≠ 0) :
    ((ordC δ v G (AddMonoidAlgebra.single G r) : ℤ) : WithTop ℤ) = v r + (frW δ G : WithTop ℤ) := by
  have hv : v r ≠ ⊤ := fun h => hr ((AddValuation.top_iff v).1 h)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hv
  simp only [ordC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, ← hn, WithTop.untopD_coe]
  push_cast; rfl

theorem ordC_mul (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G G' : WTZ E} {f g : AC Z}
    (hf : f ∈ AG Z G) (hg : g ∈ AG Z G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    ordC δ v (G + G') (f * g) = ordC δ v G f + ordC δ v G' g := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  have hs : s ≠ 0 := fun h => hg0 (by simp [h])
  rw [AddMonoidAlgebra.single_mul_single]
  apply WithTop.coe_injective
  rw [ordC_single δ v _ (mul_ne_zero hr hs)]
  push_cast
  rw [ordC_single δ v _ hr, ordC_single δ v _ hs, AddValuation.map_mul, frW_add]
  push_cast
  ac_rfl

theorem ordC_smul (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G : WTZ E} {f : AC Z} (a : Om Z)
    (hf : f ∈ AG Z G) (hf0 : f ≠ 0) (ha : a ≠ 0) :
    ((ordC δ v G (a • f) : ℤ) : WithTop ℤ) = v a + (ordC δ v G f : WithTop ℤ) := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  rw [AddMonoidAlgebra.smul_single', ordC_single δ v _ (mul_ne_zero ha hr), ordC_single δ v _ hr,
    AddValuation.map_mul, add_assoc]

abbrev sgOf (P : Om Z →+* ℂ) : c.F →+* ℂ := P.comp (algebraMap c.F (Om Z))

def PAlg (P : Om Z →+* ℂ) : Om Z →ₐ[c.F] CAt (sgOf P) :=
  { P with commutes' := fun _ => rfl }

def CBase (h : GenFrEx Xo c) (Z : Comp Xo c) (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ P, FrMap (PAlg P) (genFr h Z) (yP P)

def nrmC (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (G : WTZ E) (x : AC Z) (P : Om Z →+* ℂ) : ℝ :=
  ‖P (x.coeff G)‖ * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i)


variable (Xo c) in
def FnNe (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) : Prop := ∀ σ y i, fn σ y i ≠ 0

section nrm

variable (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
  (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

theorem nrmC_zero (G : WTZ E) (P : Om Z →+* ℂ) : nrmC fn yP G 0 P = 0 := by
  simp only [nrmC, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero, norm_zero, zero_mul]

theorem nrmC_single (G : WTZ E) (r : Om Z) (P : Om Z →+* ℂ) :
    nrmC fn yP G (AddMonoidAlgebra.single G r) P = ‖P r‖ * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i) := by
  simp only [nrmC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

theorem nrmC_pos (hfn : FnNe Xo c fn) {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G) (hf0 : f ≠ 0) :
    0 < nrmC fn yP G f P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  rw [nrmC_single]
  refine mul_pos (norm_pos_iff.2 ((map_ne_zero P).2 hr)) (Finset.prod_pos fun i _ => ?_)
  exact zpow_pos (abs_pos.2 (hfn _ _ i)) _

theorem nrmC_mul (hfn : FnNe Xo c fn) {G G' : WTZ E} {f g : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G)
    (hg : g ∈ AG Z G') : nrmC fn yP (G + G') (f * g) P = nrmC fn yP G f P * nrmC fn yP G' g P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  rw [AddMonoidAlgebra.single_mul_single, nrmC_single, nrmC_single, nrmC_single, map_mul, norm_mul]
  have : ∏ i, |fn _ (yP P) i| ^ (-exZ Dw (G + G') i) =
      (∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i)) * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G' i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [exZ_add, neg_add, zpow_add₀ (abs_ne_zero.2 (hfn _ _ i))]
  rw [this]; ring

theorem nrmC_smul {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (a : Om Z) (hf : f ∈ AG Z G) :
    nrmC fn yP G (a • f) P = ‖P a‖ * nrmC fn yP G f P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  rw [AddMonoidAlgebra.smul_single', nrmC_single, nrmC_single, map_mul, norm_mul, mul_assoc]

end nrm


variable (Xo c) in
def FnConj (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ Z (G : WTZ E) (x : AC Z) (P : Om Z →+* ℂ),
    nrmC fn (yP Z) G x ((starRingEnd ℂ).comp P) = nrmC fn (yP Z) G x P

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfD
section
noncomputable section

namespace Formalism.L2.Pj.CompSplitPfD

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology

theorem cspD_gen {X : Type} [TopologicalSpace X] [QuasiSober X] {W : Set X} (hW : W ∈ irreducibleComponents X) :
    IsGenericPoint hW.1.genericPoint W := by
  have h1 := hW.1.isGenericPoint_genericPoint_closure
  rwa [(isClosed_of_mem_irreducibleComponents W hW).closure_eq] at h1

theorem cspD_max {X : Type} [TopologicalSpace X] [T0Space X] {W : Set X}
    (hW : W ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η W) (z : X) (hz : z ⤳ η) : z = η := by
  have hWc : closure ({η} : Set X) = W := hη
  have h1 : closure ({η} : Set X) ⊆ closure {z} := specializes_iff_closure_subset.mp hz
  have hirr : IsIrreducible (closure ({z} : Set X)) := isIrreducible_singleton.closure
  have h2 : closure ({z} : Set X) ⊆ W := hW.2 hirr (hWc ▸ h1)
  have h3 : closure ({z} : Set X) = closure {η} := le_antisymm (hWc ▸ h2) h1
  exact (inseparable_iff_closure_eq.mpr h3).eq

theorem cspD_disj {X : Type} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    (hloc : ∀ x : X, ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → X), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by
  rw [Set.disjoint_left]
  intro x hxZ hxZ'
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η Z := ⟨_, cspD_gen hZ⟩
  obtain ⟨η', hη'⟩ : ∃ η', IsGenericPoint η' Z' := ⟨_, cspD_gen hZ'⟩
  have s1 : η ⤳ x := by rw [specializes_iff_mem_closure, hη.def]; exact hxZ
  have s2 : η' ⤳ x := by rw [specializes_iff_mem_closure, hη'.def]; exact hxZ'
  obtain ⟨Y, tY, g, hg, ⟨y, rfl⟩, hY⟩ := hloc x
  have hU : IsOpen (Set.range g) := hg.isOpen_range
  obtain ⟨a, ha⟩ : η ∈ Set.range g := s1.mem_open hU ⟨y, rfl⟩
  obtain ⟨b, hb⟩ : η' ∈ Set.range g := s2.mem_open hU ⟨y, rfl⟩
  have hind := hg.toIsEmbedding.toIsInducing
  have maxa : ∀ a', a' ⤳ a → a' = a := fun a' h => hg.injective (by
    have h' : g a' ⤳ g a := h.map hg.continuous
    rw [ha] at h' ⊢; exact cspD_max hZ hη _ h')
  have maxb : ∀ b', b' ⤳ b → b' = b := fun b' h => hg.injective (by
    have h' : g b' ⤳ g b := h.map hg.continuous
    rw [hb] at h' ⊢; exact cspD_max hZ' hη' _ h')
  have ya : a ⤳ y := hind.specializes_iff.mp (by rw [ha]; exact s1)
  have yb : b ⤳ y := hind.specializes_iff.mp (by rw [hb]; exact s2)
  have hab := hY a b y maxa maxb ya yb
  apply hne
  calc Z = closure {η} := hη.def.symm
    _ = closure {η'} := by rw [← ha, ← hb, hab]
    _ = Z' := hη'.def

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem cspD_smooth (Xo : Moduli Dw l) (c : Coeff l) :
    Smooth (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
  first
    | (haveI := Xo.smooth; exact MorphismProperty.pullback_snd _ _ inferInstance)
    | (haveI := Xo.smooth; infer_instance)
    | (haveI := Xo.smooth; haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s; infer_instance)

theorem cspD_local (Xo : Moduli Dw l) (c : Coeff l) (x : Xo.XF c) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → Xo.XF c), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (Xo.XF c).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have hsm := cspD_smooth Xo c
  have h1 := HasRingHomProperty.appLE (P := @Smooth)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp; trivial)
  let ψ : c.F →+* Γ(Xo.XF c, V) :=
    ((pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)).appLE ⊤ V (fun p _ => by simp; trivial)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra c.F Γ(Xo.XF c, V) := ψ.toAlgebra
  have : Algebra.Smooth c.F Γ(Xo.XF c, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := c.F)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) c.F) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) c.F) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))

theorem cspD_comp_disj (Xo : Moduli Dw l) (c : Coeff l) (Z Z' : Comp Xo c) (hne : Z ≠ Z') :
    Disjoint (Z : Set (Xo.XF c)) Z' := cspD_disj (cspD_local Xo c) Z Z' Z.2 Z'.2 (fun h => hne (Subtype.ext h))

end Formalism.L2.Pj.CompSplitPfD
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FrameProofs
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Open

variable (Xo : Moduli Dw l) (c : Coeff l)

def BorDesc : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' →
    ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R) (yq : FrPt Xo c q.R),
      FrMap φ yp y → FrMap ψ yq y' →
      ∃ (r : TRing c.F) (α : p.R →ₐ[c.F] r.R) (β : q.R →ₐ[c.F] r.R) (χ : r.R →ₐ[c.F] S)
        (z z' : FrPt Xo c r.R) (t₀ : Ix Dw → (r.R)ˣ),
        χ.comp α = φ ∧ χ.comp β = ψ ∧ FrMap α yp z ∧ FrMap β yq z' ∧ FrBor t₀ z z' ∧
          ∀ i, χ (t₀ i : r.R) = (t i : S)

def IntLatU : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io), letI := io.toAlgebra; y'.1.x = y.1.x →
    (∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧
      ∀ i, IsCombAt y.1.x (y.1.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.1.u τ i)) ∧
    ∀ (a : T.Frˣ) (pm : Gx y'.1.x ⟶ Gx y.1.x),
      pm ≫ (CartesianMonoidalCategory.snd (Over.mk y.1.x) Xo.univ.t.G).left =
          (CartesianMonoidalCategory.snd (Over.mk y'.1.x) Xo.univ.t.G).left →
      pm ≫ (CartesianMonoidalCategory.fst (Over.mk y.1.x) Xo.univ.t.G).left =
          (CartesianMonoidalCategory.fst (Over.mk y'.1.x) Xo.univ.t.G).left →
      (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.1.x).U i ≤ pm ⁻¹ᵁ (PPx y.1.x).U i),
        (pm.appLE _ _ h).hom (scal y.1.x (a : T.Fr) i * y.1.s.f i) = y'.1.s.f i) →
      valV T.V (a : T.Fr) = 1

end Open

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem wtField_of (hD : BorDesc Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  have key : ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R)
      (yq : FrPt Xo c q.R), FrMap φ yp y → FrMap ψ yq y' → ψ (f q yq) = wchar (ex Dw a n) t * φ (f p yp) := by
    intro p q φ ψ yp yq hp hq
    obtain ⟨r, α, β, χ, z, z', t₀, hα, hβ, hz, hz', hb₀, ht⟩ := hD S t y y' hb p q φ ψ yp yq hp hq
    rw [← hα, ← hβ, AlgHom.comp_apply, AlgHom.comp_apply, ← hf.1 p r α yp z hz, ← hf.1 q r β yq z' hz',
      hf.2 r t₀ z z' hb₀, map_mul]
    congr 1
    simp only [wchar, map_prod, map_pow, ht]
  unfold evR evalAt
  rw [dite_eq_left hy, dite_eq_left hy']
  exact key _ _ _ _ _ _ hy.choose_spec.choose_spec.choose_spec hy'.choose_spec.choose_spec.choose_spec

theorem valV_algebraMap_unit (T : CDVR) {u : T.V} (hu : IsUnit u) :
    valV T.V (algebraMap T.V T.Fr u) = 1 := by
  unfold valV
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro h
  exact (IsDiscreteValuationRing.maximalIdeal T.V).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem intDiagUnit_of (hL : IntLatU Xo c) : IntDiagUnit Xo c := by
  intro T io y y' t hb k
  let := io.toAlgebra
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hb
  obtain ⟨hA, hG⟩ := (show IntLatU Xo c from hL) T io y y' hx
  rcases k with _ | ⟨τ, i⟩
  · exact hG (t none) pm h1 h2 h3
  obtain ⟨A, hdet, hAc⟩ := hA τ

  have hrow : ∀ i', ∃ cf : Fin (Dw.mult τ) → T.Fr, cf i' = (t (some ⟨τ, i'⟩) : T.Fr) ∧
      (∀ j, i' < j → cf j = 0) ∧ ∀ j, algebraMap T.V T.Fr (A i' j) = cf j := by
    intro i'
    obtain ⟨cf, hci, hcz, hcomb⟩ := hu τ i'
    have htan : IsTanAt y.1.x (y'.1.u τ i') := hx ▸ y'.1.tan τ i'
    obtain ⟨a0, -, huniq⟩ := y.1.basis τ (y'.1.u τ i') htan (y'.1.eig τ i')
    have e1 := huniq cf hcomb
    have e2 := huniq _ (hAc i')
    exact ⟨cf, hci, hcz, fun j => congrFun (e2.trans e1.symm) j⟩
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hlow : A.IsLowerTriangular := by
    intro i' j hij
    obtain ⟨cf, -, hcz, hA'⟩ := hrow i'
    apply hinj
    rw [hA' j, hcz j hij, map_zero]
  rw [Matrix.det_of_isLowerTriangular A hlow, IsUnit.prod_univ_iff] at hdet
  obtain ⟨cf, hci, -, hA'⟩ := hrow i
  rw [← hci, ← hA' i]
  exact valV_algebraMap_unit T (hdet i)

end Proofs

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IntAllFree
section
noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def IntAll : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → T.FinRes →
    ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr),
      ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧
        letI := io.toAlgebra; letI := io'.toAlgebra
        ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
          (∀ a : T.V, φ (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ∧ FrMap φ y z ∧ FrBor t z y'.1

end Formalism.L2.PjFree
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IsExpChart
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

section Exp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

abbrev dL (Dw : Datum H) : ℕ := Fintype.card (Lt1 Dw)

def ltIdx (Dw : Datum H) : Lt1 Dw ≃ Fin (dL Dw) := Fintype.equivFin _

def addP {S : Type} [CommRing S] : Fin 1 × Fin (dL Dw) → MvPolynomial (Fin 2 × Fin (dL Dw)) S :=
  fun p => X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2)

def actP {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S] (a : 𝓞 E) :
    Fin 1 × Fin (dL Dw) → MvPolynomial (Fin 1 × Fin (dL Dw)) S :=
  fun p => C (algebraMap c.F S (embK c ((ltIdx Dw).symm p.2).1 a)) * X p

variable {S : Type} [CommRing S] [Algebra c.F S]

variable (y : FrPt Xo c S)

structure IsExpChart (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G) : Prop where
  zero : ∀ m, homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m) ≫
    x (m + 1) = x m
  law : ∀ m, homAt y.x (jetSubstP m (addP (Dw := Dw) (S := S))) ≫ x m =
    jpt y (dL Dw) x m (0 : Fin 2) * jpt y (dL Dw) x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ Xo.univ.t.act.act a = homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a)) ≫ x m
  tan : ∀ ℓ : Lt1 Dw, IsCombAt y.x
    (fun j : Fin (dL Dw) => (homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left)
    (fun j => if j = ltIdx Dw ℓ then 1 else 0) (y.u ℓ.1 ℓ.2)

variable (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G)

abbrev ExpFr (m : ℕ) : Type :=
  LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (1 : ℤ))

def eAt (e : ∀ m, ExpFr y x m) (m : ℕ) (a : 𝓞 E) :=
  LB.pullGen Xo.univ.t.PP.L _ _ (e m) (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left

def betaφ (a : 𝓞 E) : Fin 4 → (Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) :=
  ![(Xo.univ.t.act.act (1 + a * H.bar a)).left, (Xo.univ.t.act.act a).left, 𝟙 _,
    (Xo.univ.t.act.act (a * H.bar a)).left]

def betaε : Fin 4 → ℤ := ![1, -2, -1, -1]

structure IsExpGauge (e : ∀ m, ExpFr y x m) : Prop where
  gen : ∀ m, (e m).IsGen
  trunc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (e (m + 1))
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left)
    (e m)
  rig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (e 0) (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left)
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)
  coc : ∀ a : 𝓞 E, ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) ∧
    ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eAt y x e m (1 + a * H.bar a))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eAt y x e m a) 2)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (e m) (eAt y x e m (a * H.bar a)))))

def IsExpGerm (e : ∀ m, ExpFr y x m) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y (dL Dw) m 1)))
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y (dL Dw) m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (e m) k) ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (x m) τ (toΓ _ (psJet m f))

end Exp

def expVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {S : Type} [CommRing S]
    (f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (α : Lt1 Dw →₀ ℕ) : S :=
  (α.prod fun _ n => (n.factorial : S)) *
    MvPowerSeries.coeff (Finsupp.mapDomain (fun ℓ => ((0 : Fin 1), ltIdx Dw ℓ)) α) f

end Formalism.L2.Pj
end
end

