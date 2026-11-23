module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBFr
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmonicValueIntegral
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0004

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

section JetSubst

variable {S : Type} [CommRing S] {κ κ' : Type}

theorem jetSubstP_congr (m : ℕ) (φ ψ : κ → MvPolynomial κ' S) (h : ∀ i, φ i - ψ i ∈ orig S κ' ^ (m + 1)) :
    (jetSubstP m φ : Jet S κ m →ₐ[S] Jet S κ' m) = jetSubstP m ψ := by
  unfold jetSubstP jetMap
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.eq]
  have hc : MvPolynomial.constantCoeff (φ i) = MvPolynomial.constantCoeff (ψ i) := by
    have h1 : φ i - ψ i ∈ orig S κ' := Ideal.pow_le_self (Nat.succ_ne_zero m) (h i)
    have h2 : orig S κ' ≤ RingHom.ker (MvPolynomial.constantCoeff (R := S) (σ := κ')) := by
      unfold orig
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp
    have h3 := h2 h1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h3
    exact h3
  rw [hc]
  convert h i using 1
  ring

theorem jetSubstP_trunc (m : ℕ) (φ : κ → MvPolynomial κ' S) :
    (jetTrunc : Jet S κ' (m + 1) →ₐ[S] Jet S κ' m).comp (jetSubstP (m + 1) φ) =
      (jetSubstP m φ).comp (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) := by
  unfold jetSubstP jetMap jetTrunc liftJet
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  rfl

theorem rename_mem_orig_pow {κ'' : Type} (f : κ' → κ'') (n : ℕ) {p : MvPolynomial κ' S} (hp : p ∈ orig S κ' ^ n) :
    MvPolynomial.rename f p ∈ orig S κ'' ^ n := by
  have hle : Ideal.map (MvPolynomial.rename f : MvPolynomial κ' S →ₐ[S] MvPolynomial κ'' S) (orig S κ') ≤
      orig S κ'' := by
    unfold orig
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨f j, (MvPolynomial.rename_X f j).symm⟩
  have hm := Ideal.mem_map_of_mem (MvPolynomial.rename f : MvPolynomial κ' S →ₐ[S] MvPolynomial κ'' S) hp
  rw [Ideal.map_pow] at hm
  exact Ideal.pow_right_mono hle n hm

theorem psIn_succ_sub {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (g : MvPowerSeries (Fin n × Fin d) S) :
    psIn d (m + 1) r g - psIn d m r g ∈ orig S (Fin n' × Fin d) ^ (m + 1) := by
  unfold psIn
  rw [← map_sub]
  apply rename_mem_orig_pow
  unfold psTrunc
  have memD : ∀ (k : ℕ) (e : (Fin n × Fin d) →₀ ℕ),
      e ∈ (degLE k : Finset ((Fin n × Fin d) →₀ ℕ)) ↔ (e.sum fun _ a => a) ≤ k := by
    intro k e
    unfold degLE
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      refine ⟨⟨fun i => ⟨e i, ?_⟩, ?_⟩, h⟩
      · have hle : e i ≤ e.sum fun _ a => a := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
          exact Finset.single_le_sum (f := fun j => e j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      · ext i
        simp
  have monoMem : ∀ (k : ℕ) (e : (Fin n × Fin d) →₀ ℕ) (c : S), k ≤ (e.sum fun _ a => a) →
      MvPolynomial.monomial e c ∈ orig S (Fin n × Fin d) ^ k := by
    intro k e c hk
    have hmem : (e.prod fun i a => MvPolynomial.X i ^ a) ∈ orig S (Fin n × Fin d) ^ (e.sum fun _ a => a) := by
      simp only [Finsupp.prod, Finsupp.sum]
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Ideal.prod_mem_prod
      intro i _
      apply Ideal.pow_mem_pow
      unfold orig
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [MvPolynomial.monomial_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk hmem)
  have hsub : (degLE m : Finset ((Fin n × Fin d) →₀ ℕ)) ⊆ degLE (m + 1) := by
    intro e he
    rw [memD] at he ⊢
    omega
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  apply Ideal.sum_mem
  intro e he
  rw [Finset.mem_sdiff, memD, memD] at he
  apply monoMem
  omega

end JetSubst

section Series

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι)
    (hJ : Good t.PP.L z J) : val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J := by
  unfold scaleGenG val gm
  have hz : r z ∈ t.PP.L.wchart φ fun k => J (r ≫ φ k) := by
    unfold Good at hJ
    unfold LB.wchart
    show r z ∈ (⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k))) : Set _)
    rw [Set.mem_iInter]
    intro k
    have hk := hJ (r ≫ φ k)
    simpa using hk
  rw [dite_eq_left hz, dite_eq_left (show r z ∈ (⊤ : Y.Opens) from trivial)]
  dsimp only
  refine (MonoidHom.map_mul _ _ _).trans ?_
  congr 1
  apply Units.ext
  unfold pullU res
  have hz' : z ∈ r ⁻¹ᵁ (t.PP.L.wchart φ fun k => J (r ≫ φ k)) := hz
  have ht : z ∈ r ⁻¹ᵁ (⊤ : Y.Opens) := trivial
  have key := congrArg (fun f => CommRingCat.Hom.hom f (u : Γ(Y, ⊤)))
    (show Y.presheaf.map (homOfLE (le_top : t.PP.L.wchart φ (fun k => J (r ≫ φ k)) ≤ ⊤)).op ≫
        Scheme.Hom.app r (t.PP.L.wchart φ fun k => J (r ≫ φ k)) ≫
        Z.presheaf.germ (r ⁻¹ᵁ t.PP.L.wchart φ fun k => J (r ≫ φ k)) z hz' =
        Scheme.Hom.app r ⊤ ≫ Z.presheaf.germ (r ⁻¹ᵁ ⊤) z ht by
      rw [Scheme.Hom.naturality_assoc, TopCat.Presheaf.germ_res]
      all_goals rfl)
  first
    | exact key
    | (simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
       simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
       exact key)

abbrev ρn (n m : ℕ) : jOG x0 d m n ⟶ jOG x0 d (m + 1) n :=
  homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] Jet S (Fin n × Fin d) m)

theorem exists_series {n : ℕ} {K K' : Type} [Fintype K] [Fintype K']
    (φ : ∀ m, K → ((jOG x0 d m n).left ⟶ t.G.left)) (ε : K → ℤ)
    (φ' : ∀ m, K' → ((jOG x0 d m n).left ⟶ t.G.left)) (ε' : K' → ℤ)
    (A : ∀ m, LB.Gen (LB.LinComb t.PP.L (φ m) ε)) (hA : ∀ m, (A m).IsGen)
    (B : ∀ m, LB.Gen (LB.LinComb t.PP.L (φ' m) ε')) (hB : ∀ m, (B m).IsGen)
    (hF : ∀ m, FormEq (φ m) ε (φ' m) ε')
    (hAt : ∀ m y J, Good t.PP.L y J → val (A (m + 1)) (ρn x0 d n m).left y J = val (A m) (𝟙 _) y J)
    (hBt : ∀ m y J, Good t.PP.L y J → val (B (m + 1)) (ρn x0 d n m).left y J = val (B m) (𝟙 _) y J) :
    ∃ ph : MvPowerSeries (Fin n × Fin d) S, ∀ m, ∃ u : (Jet S (Fin n × Fin d) m)ˣ,
      (u : Jet S (Fin n × Fin d) m) = psJet m ph ∧
      LB.Gen.Corr t.PP.L _ _ _ _ (A m) (scaleGenG t _ _ (unitΓ u) (B m)) := by
  have hL := t.PP.isLB
  choose U hU using fun m => exists_ratio t.PP.L hL (hF m) (A m) (hA m) (B m) (hB m)
  have hv : ∀ m, ∃ v : (Jet S (Fin n × Fin d) m)ˣ, unitΓ v = U m := fun m =>
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin n × Fin d) m))).hom.hom.toMonoidHom (U m),
      Units.ext (congrArg (fun f => CommRingCat.Hom.hom f (U m).val)
        (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin n × Fin d) m)))))⟩
  choose v hv using hv
  have hUc : ∀ m, U m = pullU (ρn x0 d n m).left ⊤ (U (m + 1)) := by
    intro m
    refine unit_ext (V := ⊤) fun y _ => ?_
    choose I hI using fun χ : (jOG x0 d m n).left ⟶ t.G.left => exists_chart hL (χ y)
    have e1 := hU m _ (𝟙 _) y I hI
    have e2 := hU (m + 1) _ (ρn x0 d n m).left y I hI
    have e3 := gm_pull (𝟙 _) (ρn x0 d n m).left y ⊤ trivial (U (m + 1))
    rw [Category.id_comp] at e3
    refine Eq.trans ?_ e3.symm
    exact (mul_inv_eq_iff_eq_mul.2 e1).symm.trans ((congrArg₂ (fun a b => a * b⁻¹) (hAt m y I hI).symm
      (hBt m y I hI).symm).trans (mul_inv_eq_iff_eq_mul.2 e2))
  have hac : ∀ m, (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) (v (m + 1)) = v m := by
    intro m
    apply toΓ_injective
    have e1 := congrArg Units.val (hv m)
    have e2 := congrArg Units.val (hv (m + 1))
    have nat := congrArg (fun f => CommRingCat.Hom.hom f ((v (m + 1) : Jet S (Fin n × Fin d) (m + 1))))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) :
        Jet S (Fin n × Fin d) (m + 1) →+* Jet S (Fin n × Fin d) m)))
    refine nat.trans (Eq.trans ?_ e1.symm)
    refine (congrArg (fun a => ((ρn x0 d n m).left.appTop).hom a) e2).trans ?_
    rw [hUc m]
    rfl
  obtain ⟨ph, hph⟩ := exists_ps_of_jets (fun m => (v m : Jet S (Fin n × Fin d) m)) hac
  refine ⟨ph, fun m => ⟨v m, (hph m).symm, corr_of_val hL fun y J hJ => ?_⟩⟩
  exact (hU m _ (𝟙 _) y J hJ).trans ((congrArg (fun u => gm (𝟙 _) y ⊤ u * val (B m) (𝟙 _) y J) (hv m).symm).trans
    (val_scale t _ _ _ _ _ y J hJ).symm)

theorem pe_trunc {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {e : ∀ m, FrTyG t x0 d x m} (htr : FrTrunc t x0 d x e) {n : ℕ}
    (φ : ℕ → Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (hφ : ∀ m i j, φ (m + 1) i j - φ m i j ∈ orig S (Fin n × Fin d) ^ (m + 1))
    (m : ℕ) (y : (jOG x0 d m n).left) (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val (peG t x0 d x e (m + 1) (φ (m + 1))) (ρn x0 d n m).left y J = val (peG t x0 d x e m (φ m)) (𝟙 _) y J := by
  have hc : (jetSubstP m fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2 :
      Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) = jetSubstP m fun p => φ m p.1 p.2 :=
    jetSubstP_congr m _ _ (fun p => hφ m p.1 p.2)
  have hcomp : (ρn x0 d n m).left ≫
      (homAt x0 (jetSubstP (m + 1) fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left =
      (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp, jetSubstP_trunc]
  unfold peG
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e (m + 1))
    (homAt x0 (jetSubstP (m + 1) fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left (ρn x0 d n m).left (z := y) (J := J)
  have h2 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e m)
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left (𝟙 _) (z := y) (J := J)
  have h3 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e (m + 1))
    (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left (z := y) (J := J)
  have h4 : val (LB.pullGen t.PP.L _ _ (e (m + 1))
      (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left y J =
      val (e m) (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left y J := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr (htr m) _
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr hJ (htr m) _
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr (htr m) _ hJ
  try unfold peG
  refine h1.trans ?_
  rw [hcomp, hc]
  refine h3.symm.trans (h4.trans ?_)
  refine (h2.trans ?_).symm
  rw [Category.id_comp]

end Series

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ScaleGenIsGen
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res h2 (ReciprocityTheory.ChartRestriction.G.Semi.res h1 x) = ReciprocityTheory.ChartRestriction.G.Semi.res (h2.trans h1) x := by
  apply Units.ext
  first
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.coe_map, MonoidHom.coe_coe]
     rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.coe_map, MonoidHom.coe_coe]
     rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl)
  | (simp [ReciprocityTheory.ChartRestriction.G.Semi.res, ← Functor.map_comp_apply])

private lemma pullU_res_lemma_2 {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.pullU f V (ReciprocityTheory.ChartRestriction.G.Semi.res h x) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (fun _ hy => h hy)) (ReciprocityTheory.ChartRestriction.G.Semi.pullU f U x) := by
  apply Units.ext
  first
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.coe_map, MonoidHom.coe_coe]
     rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
       Scheme.Hom.naturality]; rfl)
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.coe_map, MonoidHom.coe_coe]
     exact (Scheme.Hom.naturality_apply f (homOfLE h).op _).symm)
  | (simp [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, ← Scheme.Hom.naturality_apply])

private lemma pullU_comp_lemma_3 {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.pullU (g ≫ f) U x = ReciprocityTheory.ChartRestriction.G.Semi.pullU g (f ⁻¹ᵁ U) (ReciprocityTheory.ChartRestriction.G.Semi.pullU f U x) := by
  first
  | rfl
  | (apply Units.ext; rfl)
  | (apply Units.ext; simp [ReciprocityTheory.ChartRestriction.G.Semi.pullU, Scheme.comp_app])

private lemma pullGen_isGen_lemma_4 {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {c : LB.Gen (LB.LinComb L φ ε)} (hc : c.IsGen) {h : Z ⟶ Y} :
    (LB.pullGen L φ ε c h).IsGen := by
  intro i j
  have Pi : ∀ i', LB.wchart L (fun k => h ≫ φ k) i' ≤ h ⁻¹ᵁ LB.wchart L φ i' :=
    fun i' _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have T : LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart L φ j) :=
    le_inf (inf_le_left.trans (Pi i)) (inf_le_right.trans (Pi j))
  have H0 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ i) inf_le_left) (@id (Γ(Y, LB.wchart L φ i)ˣ) (c.s i)) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ i ⊓ LB.wchart L φ j ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ i k)) (inf_le_right.trans (LB.wchart_le L _ j k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (φ k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ε k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ j) inf_le_right) (@id (Γ(Y, LB.wchart L φ j)ˣ) (c.s j)) := hc i j
  have H := congrArg (fun z => ReciprocityTheory.ChartRestriction.G.Semi.res T (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ i ⊓ LB.wchart L φ j) z)) H0
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ LB.wchart L (fun k => h ≫ φ k) i) inf_le_left) (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi i) (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ i) (@id (Γ(Y, LB.wchart L φ i)ˣ) (c.s i)))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ (h ≫ φ k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ i k)) (inf_le_right.trans (LB.wchart_le L _ j k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (h ≫ φ k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ε k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ LB.wchart L (fun k => h ≫ φ k) j) inf_le_right) (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi j) (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ j) (@id (Γ(Y, LB.wchart L φ j)ˣ) (c.s j))))
  simp only [map_mul, map_prod, map_zpow, res_res_lemma, pullU_res_lemma_2, pullU_comp_lemma_3] at H ⊢
  exact H

private lemma mulGen_isGen_lemma_5 {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) :
    (LB.mulGen L φ ε φ' ε' t t').IsGen := by
  intro i j
  have Pi : ∀ i', LB.wchart L (Sum.elim φ φ') i' ≤ LB.wchart L φ (i' ∘ Sum.inl) :=
    fun i' _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have Qi : ∀ i', LB.wchart L (Sum.elim φ φ') i' ≤ LB.wchart L φ' (i' ∘ Sum.inr) :=
    fun i' _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  have H1 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) ≤ LB.wchart L φ (i ∘ Sum.inl)) inf_le_left) (@id (Γ(Y, LB.wchart L φ (i ∘ Sum.inl))ˣ) (t.s (i ∘ Sum.inl))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) ≤ φ k ⁻¹ᵁ (L.U (i (Sum.inl k)) ⊓ L.U (j (Sum.inl k))))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ (i ∘ Sum.inl) k)) (inf_le_right.trans (LB.wchart_le L _ (j ∘ Sum.inl) k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (φ k) (L.U (i (Sum.inl k)) ⊓ L.U (j (Sum.inl k))) (L.g (i (Sum.inl k)) (j (Sum.inl k))))) ^ ε k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) ≤ LB.wchart L φ (j ∘ Sum.inl)) inf_le_right) (@id (Γ(Y, LB.wchart L φ (j ∘ Sum.inl))ˣ) (t.s (j ∘ Sum.inl))) := ht _ _
  have H2 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) ≤ LB.wchart L φ' (i ∘ Sum.inr)) inf_le_left) (@id (Γ(Y, LB.wchart L φ' (i ∘ Sum.inr))ˣ) (t'.s (i ∘ Sum.inr))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) ≤ φ' k ⁻¹ᵁ (L.U (i (Sum.inr k)) ⊓ L.U (j (Sum.inr k))))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ (i ∘ Sum.inr) k)) (inf_le_right.trans (LB.wchart_le L _ (j ∘ Sum.inr) k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (φ' k) (L.U (i (Sum.inr k)) ⊓ L.U (j (Sum.inr k))) (L.g (i (Sum.inr k)) (j (Sum.inr k))))) ^ ε' k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) ≤ LB.wchart L φ' (j ∘ Sum.inr)) inf_le_right) (@id (Γ(Y, LB.wchart L φ' (j ∘ Sum.inr))ˣ) (t'.s (j ∘ Sum.inr))) := ht' _ _
  have T1 : LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) :=
    inf_le_inf (Pi i) (Pi j)
  have T2 : LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) :=
    inf_le_inf (Qi i) (Qi j)
  have G1 := congrArg (ReciprocityTheory.ChartRestriction.G.Semi.res T1) H1
  have G2 := congrArg (ReciprocityTheory.ChartRestriction.G.Semi.res T2) H2
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L (Sum.elim φ φ') i) inf_le_left)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi i) (@id (Γ(Y, LB.wchart L φ (i ∘ Sum.inl))ˣ) (t.s (i ∘ Sum.inl))) * ReciprocityTheory.ChartRestriction.G.Semi.res (Qi i) (@id (Γ(Y, LB.wchart L φ' (i ∘ Sum.inr))ˣ) (t'.s (i ∘ Sum.inr)))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ (Sum.elim φ φ' k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ i k)) (inf_le_right.trans (LB.wchart_le L _ j k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (Sum.elim φ φ' k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ (Sum.elim ε ε' k)) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L (Sum.elim φ φ') j) inf_le_right)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi j) (@id (Γ(Y, LB.wchart L φ (j ∘ Sum.inl))ˣ) (t.s (j ∘ Sum.inl))) * ReciprocityTheory.ChartRestriction.G.Semi.res (Qi j) (@id (Γ(Y, LB.wchart L φ' (j ∘ Sum.inr))ˣ) (t'.s (j ∘ Sum.inr))))
  simp only [map_mul, map_prod, map_zpow, res_res_lemma, Fintype.prod_sum_type] at G1 G2 ⊢
  exact (congrArg₂ (· * ·) G1 G2).trans (mul_mul_mul_comm _ _ _ _)

private lemma corr_pull_lemma_6 {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {a : LB.Gen (LB.LinComb L φ ε)}
    {b : LB.Gen (LB.LinComb L φ' ε')} (hab : LB.Gen.Corr L φ ε φ' ε' a b) {h : Z ⟶ Y} :
    LB.Gen.Corr L (fun k => h ≫ φ k) ε (fun k => h ≫ φ' k) ε' (LB.pullGen L φ ε a h) (LB.pullGen L φ' ε' b h) := by
  intro j j' hj hj' hjj'
  have H1 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ j) inf_le_left) (@id (Γ(Y, LB.wchart L φ j)ˣ) (a.s j)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ' j') inf_le_right) (@id (Γ(Y, LB.wchart L φ' j')ˣ) (b.s j')) :=
    hab j j' (fun k₁ k₂ e => hj k₁ k₂ (by simp only [e])) (fun k₁ k₂ e => hj' k₁ k₂ (by simp only [e]))
      (fun k k' e => hjj' k k' (by simp only [e]))
  have Pa : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have Pb : LB.wchart L (fun k => h ≫ φ' k) j' ≤ h ⁻¹ᵁ LB.wchart L φ' j' := fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have T : LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' ≤ h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := le_inf (inf_le_left.trans Pa) (inf_le_right.trans Pb)
  have H := congrArg (fun z => ReciprocityTheory.ChartRestriction.G.Semi.res T (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ j ⊓ LB.wchart L φ' j') z)) H1
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' ≤ LB.wchart L (fun k => h ≫ φ k) j) inf_le_left) (ReciprocityTheory.ChartRestriction.G.Semi.res Pa (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ j) (@id (Γ(Y, LB.wchart L φ j)ˣ) (a.s j)))) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' ≤ LB.wchart L (fun k => h ≫ φ' k) j') inf_le_right) (ReciprocityTheory.ChartRestriction.G.Semi.res Pb (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ' j') (@id (Γ(Y, LB.wchart L φ' j')ˣ) (b.s j'))))
  simp only [res_res_lemma, pullU_res_lemma_2] at H ⊢
  exact H

private lemma corr_scale_lemma_7 {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ Xo.univ.t.G.left)} {ε' : K' → ℤ}
    {v : Γ(Y, ⊤)ˣ} {a : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} {b : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')}
    (hab : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' a b) :
    LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' (scaleGen φ ε v a) (scaleGen φ' ε' v b) := by
  intro j j' hj hj' hjj'
  have H0 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ j) inf_le_left) (@id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ j)ˣ) (a.s j)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ' j') inf_le_right) (@id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ' j')ˣ) (b.s j')) := hab j j' hj hj' hjj'
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ j) inf_le_left)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ≤ ⊤) le_top) v * @id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ j)ˣ) (a.s j)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ' j') inf_le_right)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ' j' ≤ ⊤) le_top) v * @id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ' j')ˣ) (b.s j'))
  simp only [map_mul, res_res_lemma]
  rw [H0]

theorem eL_isGen (C : ChartAt Xo c y) (m : ℕ) : (eL y C.d C.x C.B.A.act C.e C.wP m).IsGen := by
  first
  | exact mulGen_isGen_lemma_5 (pullGen_isGen_lemma_4 C.prim.1) (pullGen_isGen_lemma_4 (C.frame.gen m))
  | (dsimp only [Formalism.L2.Pj.eL, Formalism.L2.Pj.pe]
     exact mulGen_isGen_lemma_5 (pullGen_isGen_lemma_4 C.prim.1) (pullGen_isGen_lemma_4 (C.frame.gen m)))

theorem scaleGen_isGen {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (v : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (hg : g.IsGen) : (scaleGen φ ε v g).IsGen := by
  intro i j
  have H := hg i j
  simp only [Formalism.L2.Pj.scaleGen, map_mul, res_res_lemma]
  rw [H]
  exact mul_left_comm _ _ _

theorem exists_tau (C : ChartAt Xo c y) (m : ℕ) :
    ∃ τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)), τ.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (eL y C.d C.x C.B.A.act C.e C.wP m) := by
  have hL := Xo.univ.t.PP.isLB
  have hch := (isChart_iff y C.d C.B.G.F C.B.A.act C.uvec C.x).1 C.chart
  obtain ⟨τ, hτ, hv⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (C.x m).left) (ε' := fun _ => (1 : ℤ)) (by
      intro U _ hU
      have hf : ∀ I : ULift.{0} (Finset (Fin 2)),
          (C.x m).left ≫ cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0] I =
            (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d =>
              (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn C.d m ![0] (C.B.A.act H.w0 j)] :
                Fin 2 → Fin C.d → MvPolynomial (Fin 1 × Fin C.d) S) p.1 p.2)).left ≫
              cφ ![jpt y C.d C.x m (0 : Fin 2), jpt y C.d C.x m (1 : Fin 2)] I :=
        fun I => GermD.formEq_eL hch m I
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, hf]
      rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
      simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]) _ (eL_isGen C m)
  exact ⟨τ, hτ, corr_of_val hL fun y' J hJ => hv _ (𝟙 _) y' J hJ⟩

theorem const_hL (C : ChartAt Xo c y) : MvPowerSeries.constantCoeff (C.B.hL S C.h H.w0) = 0 := by
  have hh0 : MvPowerSeries.constantCoeff C.h = 0 := by
    have e := Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev (n := 1) ![0, Germ.pt S (n := 1) C.d 0] (by intro p q; fin_cases p <;> simp [Germ.pt])
      C.h
    rw [C.gauge.ax0, map_zero] at e
    exact e.symm
  have hact : ∀ q, MvPowerSeries.constantCoeff (Germ.comp1 (C.B.actK S H.w0) (Germ.pt S (n := 1) C.d 0) q) = 0 := by
    intro q
    unfold Germ.comp1
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev _ (by intro p' q'; fin_cases p'; simp [Germ.pt])]
    unfold Germ.FB.actK
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, C.B.A.const, map_zero]
  unfold Germ.FB.hL
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev _ (by
    intro p q
    fin_cases p
    · simp [Germ.pt]
    · exact hact q)]
  exact hh0

theorem exists_uJ (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (m : ℕ) :
    ∃ u : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
      (u : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) := by
  have h0 : MvPowerSeries.constantCoeff (compL φ (C.B.hL S C.h H.w0)) = 0 := by
    unfold compL
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.const_subst (fun p : Fin 1 × Fin C.d => hφ p.2)]
    exact const_hL C
  have h1 : MvPowerSeries.constantCoeff (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) = 1 := by
    unfold Germ.FB.expS
    rw [PowerSeries.subst, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.const_subst (fun _ => by rw [map_neg, h0, neg_zero])]
    exact PowerSeries.constantCoeff_exp
  obtain ⟨v, hv⟩ : IsUnit (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [h1]; exact isUnit_one)
  refine ⟨⟨psJet m (v : MvPowerSeries _ S), psJet m (↑v⁻¹ : MvPowerSeries _ S), ?_, ?_⟩, ?_⟩
  · rw [← FBIdJet.psJet_mul, Units.mul_inv, FBIdJet.psJet_one]
  · rw [← FBIdJet.psJet_mul, Units.inv_mul, FBIdJet.psJet_one]
  · simp only [hv]

def eG (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ) (m : ℕ) : ExpFr y (xExp y C φ) m :=
  scaleGen _ _ (unitΓ (u m)) (LB.pullGen Xo.univ.t.PP.L _ _ (τ m) (homAt y.x (jφ φ m)).left)

theorem exists_eG (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) :
    ∃ (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1)
      (fun _ => (C.x m).left) fun _ => (1 : ℤ))) (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ),
      (∀ m, (τ m).IsGen) ∧
      (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m)) ∧
      (∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
        psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))))) ∧
      (∀ m, (eG C φ τ u m).IsGen) ∧ IsExpGaugeOf y C φ (eG C φ τ u) := by
  choose τ hτ hτc using exists_tau C
  choose u hu using exists_uJ C φ hφ
  refine ⟨τ, u, hτ, hτc, hu, fun m => ?_, ?_⟩
  · first
    | exact scaleGen_isGen _ _ _ _ (pullGen_isGen_lemma_4 (hτ m))
    | (unfold eG; exact scaleGen_isGen _ _ _ _ (pullGen_isGen_lemma_4 (hτ m)))
  · first
    | exact fun m => ⟨u m, hu m, corr_scale_lemma_7 (corr_pull_lemma_6 (hτc m))⟩
    | (intro m; exact ⟨u m, hu m, corr_scale_lemma_7 (corr_pull_lemma_6 (hτc m))⟩)
    | (intro m; refine ⟨u m, hu m, ?_⟩; unfold eG; exact corr_scale_lemma_7 (corr_pull_lemma_6 (hτc m)))

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
end
end

