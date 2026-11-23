module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem glue_units {X : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (r : ∀ i, Γ(X, U i)ˣ)
    (hr : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (r i) = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, res (le_top : U i ≤ ⊤) u = r i := by
  simp only [res] at hr ⊢
  have hc : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    obtain ⟨i, hi⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨s, hs, -⟩ : ∃! s : Γ(X, ⊤), ∀ i,
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = (r i : Γ(X, U i)) :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hc
    (fun i => ((r i : Γ(X, U i)))) (fun i j => by
      have h1 := congrArg Units.val (hr i j)
      simp only [Units.coe_map, MonoidHom.coe_coe] at h1
      exact h1)
  obtain ⟨t, ht, -⟩ : ∃! t : Γ(X, ⊤), ∀ i,
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t = (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hc
    (fun i => (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i))) (fun i j => by
      have h1 := congrArg (fun v => ((v⁻¹ : Γ(X, U i ⊓ U j)ˣ) : Γ(X, U i ⊓ U j))) (hr i j)
      simp only [← map_inv, Units.coe_map, MonoidHom.coe_coe] at h1
      exact h1)
  have hs' : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = (r i : Γ(X, U i)) :=
    fun i => hs i
  have ht' : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t =
      (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) := fun i => ht i
  have hst : s * t = 1 := by
    apply X.sheaf.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) hc
    intro i
    show (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom (s * t) =
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom 1
    rw [map_mul, map_one, hs' i, ht' i, Units.mul_inv]
  refine ⟨⟨s, t, hst, by rw [mul_comm]; exact hst⟩, fun i => ?_⟩
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mk]
  exact hs' i

theorem exists_ratio_gen {X : Scheme.{0}} {M : LB X} (hcov : ∀ x : X, ∃ i, x ∈ M.U i) {g₁ g₂ : LB.Gen M}
    (h₁ : g₁.IsGen) (h₂ : g₂.IsGen) : ∃ u : Γ(X, ⊤)ˣ, ∀ i, g₁.s i = res (le_top : M.U i ≤ ⊤) u * g₂.s i := by
  unfold LB.Gen.IsGen at h₁ h₂
  obtain ⟨u, hu⟩ := glue_units M.U hcov (fun i => g₁.s i / g₂.s i) (fun i j => by
    rw [map_div, map_div, h₁ i j, h₂ i j, mul_div_mul_left_eq_div])
  exact ⟨u, fun i => by rw [hu i, div_mul_cancel]⟩

theorem unit_eq_one_of_eSec (hGF : GlobalFnsSt) {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (u : Γ(A.left, ⊤)ˣ) (h : (eSec A).appTop.hom u.val = 1) : u = 1 := by
  unfold GlobalFnsSt at hGF
  have hsec : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    rw [Over.w]
    rfl
  obtain ⟨s, hs⟩ := (hGF S A hA).2 u.val
  have h2 : (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s = s := by
    rw [hsec]
    simp
  have hs1 : s = 1 := by
    calc s = (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s := h2.symm
      _ = (Scheme.Hom.appTop (eSec A)).hom ((Scheme.Hom.appTop A.hom).hom s) := rfl
      _ = 1 := by rw [hs, h]
  ext
  rw [← hs, hs1, map_one]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrB
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

abbrev jc (n m : ℕ) : Jet T.V (Fin n × Fin d) m →+* Jet T.Fr (Fin n × Fin d) m :=
  jetCoef (algebraMap T.V T.Fr) (Fin n × Fin d) m

theorem xL_w (m : ℕ) : (spMap (jc (d := d) 1 m) ≫ (xT m).left) ≫ I.G.G.hom =
    spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) ≫ spMap (algebraMap T.V T.Fr) := by
  rw [Category.assoc, Over.w]
  simp only [spMap_comp']
  simp only [jOG, Over.mk_hom, Category.comp_id, spMap_comp']
  congr 1
  ext r
  simp only [jc, jetCoef, RingHom.comp_apply]
  erw [Ideal.Quotient.lift_mk]
  simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  rfl

def xL (m : ℕ) : Sp (Jet T.Fr (Fin 1 × Fin d) m) ⟶ I.t'.G.left :=
  I.m2.cart.1.lift (spMap (jc (d := d) 1 m) ≫ (xT m).left) (spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)))
    (xL_w I xT m)

theorem xL_fst (m : ℕ) : xL I xT m ≫ I.m2.φ = spMap (jc (d := d) 1 m) ≫ (xT m).left := I.m2.cart.1.lift_fst _ _ _

theorem xL_snd (m : ℕ) : xL I xT m ≫ I.t'.G.hom = spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) := I.m2.cart.1.lift_snd _ _ _

def xP (m : ℕ) : jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G :=
  Over.homMk (xL I xT m) (by
    show xL I xT m ≫ I.t'.G.hom = spMap _ ≫ 𝟙 _
    rw [xL_snd, Category.comp_id])

def xU (m : ℕ) : (letI := io.toAlgebra; jO y.1 d m 1) ⟶ Xo.univ.t.G :=
  letI := io.toAlgebra
  Over.homMk (xL I xT m ≫ I.m1.φ) (by
    show (xL I xT m ≫ I.m1.φ) ≫ Xo.univ.t.G.hom = spMap _ ≫ y.1.x
    rw [Category.assoc, I.m1.cart.1.w, ← Category.assoc, xL_snd])

theorem ext2 {Z : Scheme.{0}} {a b : Z ⟶ I.t'.G.left} (h1 : a ≫ I.m2.φ = b ≫ I.m2.φ)
    (h2 : a ≫ I.t'.G.hom = b ≫ I.t'.G.hom) : a = b := I.m2.cart.1.hom_ext h1 h2

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)

attribute [local instance] Over.cartesianMonoidalCategory

namespace ExpBijectiveUniformisation

section Help

variable {X Y Z : Scheme.{0}}

lemma wchart_comp_le (L : LB X) (g : Y ⟶ X) (z : Z ⟶ Y) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : PUnit.{1} => z ≫ g) (fun _ => j 0) ≤ z ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => g) j := by
  intro y hy
  have h1 : (z ≫ g).base y ∈ L.U (j 0) := Set.mem_iInter.1 hy ⟨⟩
  show z.base y ∈ (⋂ k : Fin 1, g.base ⁻¹' (L.U (j k) : Set X))
  refine Set.mem_iInter.2 fun k => ?_
  rw [Fin.fin_one_eq_zero k]
  exact h1

def genCast {L L' : LB X} (h : L = L') {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (b : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L' φ ε) :=
  h ▸ b

def sumQ {X1 Xn : Type} [AddCommGroup X1] [AddCommGroup Xn] {n : ℕ} (xe : Xn ≃+ (Fin n → X1)) (Q : X1 → ℤ) :
    Xn → ℤ :=
  fun x => ∑ i, Q (xe x i)

end Help

section GermN

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def jcN (V F : Type) [CommRing V] [Field F] [Algebra V F] (d n m : ℕ) (i : Fin n) :
    Sp (Jet F (Fin n × Fin d) m) ⟶ Sp (Jet V (Fin 1 × Fin d) m) :=
  spMap (((jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m) :
      Jet F (Fin 1 × Fin d) m →+* Jet F (Fin n × Fin d) m).comp
    (jetCoef (algebraMap V F) (Fin 1 × Fin d) m))

def jptN {V : Type} [CommRing V] {t : SAB H (Sp V)} {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (F : Type)
    [Field F] [Algebra V F] (n m : ℕ) (i : Fin n) : Sp (Jet F (Fin n × Fin d) m) ⟶ t.G.left :=
  jcN V F d n m i ≫ (xT m).left

def IsGermN {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {t : SAB H (Sp V)} (P : PELUnif I t) {d n : ℕ}
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V)
    (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t)
    {D' : DegData V I} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Sp V)} [GrpObj G']
    [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} (pG : IsPowGrp G' t.G n)
    {U' : Unif I D' A' G'} (PU : UnifPowOf pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] (q : ℕ)
    (σ' : U'.toUnifPre.SecGF F q) (f : PS F n d) : Prop :=
  ∀ m, ∃ (z : Sp (Jet F (Fin n × Fin d) m) ⟶ (UnifPre.GF (R := V) (G := G') F).left)
    (τ : LB.Gen (LB.LinComb U'.LG.L (K := PUnit.{1}) (fun _ => z ≫ UnifPre.gFK (R := V) (G := G') F)
      (fun _ => (q : ℤ))))
    (b : LB.Gen (LB.LinComb P.U.LG.L (K := Fin n)
      (fun i => (z ≫ UnifPre.gFK (R := V) (G := G') F) ≫ (pG.pr i).left) (fun _ => (q : ℤ)))),
    z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
      spMap (algebraMap F (Jet F (Fin n × Fin d) m)) ∧
    (∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i) ∧
    GeneratorPullback.MapsAt P.U.LG.L U'.LG.L (fun i => (pG.pr i).left) PU.wL (z ≫ UnifPre.gFK (R := V) (G := G') F) q τ b ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (genCast (congrArg RigLB.L P.bundle) _ _ b)
      (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
        LB.pullGen t.PP.L _ _ (genPowG t _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m) q) (jcN V F d n m i)) ∧
    ∀ j : Fin 1 → U'.LG.L.ι,
      ((Sp (Jet F (Fin n × Fin d) m)).presheaf.map
          (homOfLE (wchart_comp_le U'.LG.L (UnifPre.gFK (R := V) (G := G') F) z j)).op).hom
        ((z.app _).hom (σ'.f j)) =
      ((Sp (Jet F (Fin n × Fin d) m)).presheaf.map (homOfLE le_top).op).hom (toΓ _ (psJet m f)) *
        (τ.s (fun _ => j 0)).val

end GermN

section St

open IsLocalRing

end St

end ExpBijectiveUniformisation

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqC
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

namespace GaugeR

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

@[reducible] def barStar (H : Host E) : StarRing (𝓞 E) where
  star := H.bar
  star_involutive a := by
    apply RingOfIntegers.ext
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  star_mul a b := by
    show H.bar (a * b) = H.bar b * H.bar a
    rw [map_mul, mul_comm]
  star_add a b := map_add H.bar a b

variable {H : Host E} {Dw : Datum H} {l : Level H}

def chi (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (σ : E →+* ℂ) : 𝓞 E →+* S :=
  (algebraMap c.F S).comp (embK c σ)

theorem embK_conj (c : Coeff l) (σ : E →+* ℂ) (a : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate σ) a = embK c σ (H.bar a) := by
  apply Subtype.ext
  show (ComplexEmbedding.conjugate σ) (a : E) = σ ((H.bar a : 𝓞 E) : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, NumberField.IsCMField.complexEmbedding_complexConj]

theorem hunit_chi (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (σ τ : E →+* ℂ) (h : σ ≠ τ) :
    ∃ a, IsUnit (chi c S σ a - chi c S τ a) := by
  classical
  have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
    by_contra hc
    push_neg at hc
    apply h
    ext x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hc a) (hc b)
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_⟩
  have hne : embK c σ a - embK c τ a ≠ 0 := by
    intro h0
    apply ha
    exact congrArg (fun z : c.F => (z : ℂ)) (sub_eq_zero.mp h0)
  have hu := (hne.isUnit).map (algebraMap c.F S)
  simpa [chi, map_sub] using hu

def nu (Dw : Datum H) : Lt1 Dw ≃ Fin 1 × Fin (dL Dw) where
  toFun ℓ := ((0 : Fin 1), ltIdx Dw ℓ)
  invFun p := (ltIdx Dw).symm p.2
  left_inv ℓ := by simp
  right_inv p := Prod.ext (Subsingleton.elim _ _) (by simp)

theorem exists_embDomain (x : Fin 1 × Fin (dL Dw) →₀ ℕ) : ∃ y, Finsupp.embDomain (nu Dw).toEmbedding y = x := by
  refine ⟨Finsupp.equivMapDomain (nu Dw).symm x, ?_⟩
  rw [Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding, ← Finsupp.equivMapDomain_eq_mapDomain]
  ext p
  simp [Finsupp.equivMapDomain_apply]

theorem degree_embDomain {α β : Type} (f : α ↪ β) (y : α →₀ ℕ) : (Finsupp.embDomain f y).degree = y.degree := by
  classical
  show ∑ i ∈ (Finsupp.embDomain f y).support, (Finsupp.embDomain f y) i = ∑ i ∈ y.support, y i
  rw [Finsupp.support_embDomain, Finset.sum_map]
  simp

private theorem coeff_rename_emb_lemma {S : Type} [CommRing S] (p : MvPowerSeries (Lt1 Dw) S)
    (y : Lt1 Dw →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) (MvPowerSeries.rename (nu Dw).toEmbedding p) =
      MvPowerSeries.coeff y p :=
  MvPowerSeries.coeff_embDomain_rename _ _ _

theorem rename_rescale {S : Type} [CommRing S] (s : Fin 1 × Fin (dL Dw) → S) (p : MvPowerSeries (Lt1 Dw) S) :
    MvPowerSeries.rename (nu Dw).toEmbedding (MvPowerSeries.rescale (fun ℓ => s (nu Dw ℓ)) p) =
      MvPowerSeries.rescale s (MvPowerSeries.rename (nu Dw).toEmbedding p) := by
  ext x
  obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) x
  simp only [coeff_rename_emb_lemma, MvPowerSeries.coeff_rescale, Finsupp.prod_embDomain] <;> rfl

def sc (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (a : 𝓞 E) : Fin 1 × Fin (dL Dw) → S :=
  fun p => algebraMap c.F S (embK c ((ltIdx Dw).symm p.2).1 a)

theorem ratio_exp (hR : GaugeRatioSt) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (r : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (h1 : MvPowerSeries.constantCoeff r = 1)
    (hr : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r * MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r) :
    ∃ q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, MvPowerSeries.constantCoeff q = 0 ∧
      (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
          Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      r = PowerSeries.subst q (PowerSeries.exp S) := by
  letI : StarRing (𝓞 E) := barStar H
  let r' : MvPowerSeries (Lt1 Dw) S := fun y => MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r
  have hcr' : ∀ y, MvPowerSeries.coeff y r' = MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r :=
    fun y => rfl
  have hrr : MvPowerSeries.rename (nu Dw).toEmbedding r' = r := by
    ext x
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) x
    rw [coeff_rename_emb_lemma, hcr']
  have hinj : ∀ p p' : MvPowerSeries (Lt1 Dw) S,
      MvPowerSeries.rename (nu Dw).toEmbedding p = MvPowerSeries.rename (nu Dw).toEmbedding p' → p = p' := by
    intro p p' hpp
    ext y
    have hc := congrArg (MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y)) hpp
    simpa only [coeff_rename_emb_lemma] using hc
  have hsc : ∀ b : 𝓞 E, (fun ℓ : Lt1 Dw => sc (Dw := Dw) c S b (nu Dw ℓ)) = fun ℓ => chi c S ℓ.1 b := by
    intro b
    funext ℓ
    simp [sc, chi, nu]
  have hscale : ∀ (b : 𝓞 E) (p : MvPowerSeries (Lt1 Dw) S),
      MvPowerSeries.rename (nu Dw).toEmbedding (scaleBy (rk := Dw.mult) (chi c S) b p) =
        MvPowerSeries.rescale (sc (Dw := Dw) c S b) (MvPowerSeries.rename (nu Dw).toEmbedding p) := by
    intro b p
    (rw [← rename_rescale, hsc b]) <;> rfl
  have hr0' : MvPowerSeries.constantCoeff r' = 1 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcr', Finsupp.embDomain_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h1]
  have hr' : ∀ a : 𝓞 E, scaleBy (rk := Dw.mult) (chi c S) (1 + a * star a) r' =
      scaleBy (rk := Dw.mult) (chi c S) a r' ^ 2 * r' * scaleBy (rk := Dw.mult) (chi c S) (a * star a) r' := by
    intro a
    apply hinj
    rw [map_mul, map_mul, map_pow, hscale, hscale, hscale, hrr]
    exact hr a
  have hcc : ∀ (σ : E →+* ℂ) (a : 𝓞 E), chi c S (ComplexEmbedding.conjugate σ) a = chi c S σ (star a) := by
    intro σ a
    simp only [chi, RingHom.comp_apply]
    (rw [embK_conj]) <;> rfl
  obtain ⟨q', hq0, hqdeg, hqpair, hqexp⟩ :=
    hR (𝓞 E) S (E →+* ℂ) Dw.mult (chi c S) ComplexEmbedding.conjugate hcc
      (fun σ τ hστ => hunit_chi c S σ τ hστ) r' hr0' hr'
  have hq0r : MvPowerSeries.constantCoeff (MvPowerSeries.rename (nu Dw).toEmbedding q') = 0 := by
    rw [MvPowerSeries.constantCoeff_rename, hq0]
  refine ⟨MvPowerSeries.rename (nu Dw).toEmbedding q', hq0r, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) m
    rw [coeff_rename_emb_lemma] at hm
    rw [degree_embDomain]
    exact hqdeg y hm
  · intro ℓ ℓ' hm
    have hsum : Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 + Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1 =
        Finsupp.embDomain (nu Dw).toEmbedding (Finsupp.single ℓ 1 + Finsupp.single ℓ' 1) := by
      (rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]) <;> rfl
    rw [hsum, coeff_rename_emb_lemma] at hm
    exact hqpair ℓ ℓ' hm
  · ext m
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) m
    rw [← hrr, coeff_rename_emb_lemma, hqexp,
      PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0),
      PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0r)]
    congr 1
    funext d
    rw [← map_pow, coeff_rename_emb_lemma]

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

