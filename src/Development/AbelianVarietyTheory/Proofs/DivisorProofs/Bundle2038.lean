module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeLinearInKodairaSpencerMatrixOfI
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole

theorem exists_snd_ev_eq_sum_of_ksIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (K : Type) [Field K] [Algebra c.F K] (P₀ : FrPt Xo c K), KSIso (psiSet H) P₀ → ∀ (U : TF.Y.X.Opens), ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U → ∃ δ : HIx Dw (psiSet H) → Γ(TF.Y.X, U) → K, ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hy : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → spMap (FlagTan.red c K).toRingHom ≫ y' = frX P₀ → ∀ (M : HIx Dw (psiSet H) → K), FlagTan.IsKS (psiSet H) P₀ (y' ≫ pullback.fst _ _) M → ∀ r, (ev (y' ≫ TF.Y.j) U hy r).snd = ∑ k, M k * δ k r := by
  intro E _ _ _ H Dw l Xo c TF K _ _ P₀ hKS U hU
  obtain ⟨X, hX, hP, hk⟩ := hKS
  let S := TrivSqZeroExt K (HIx Dw (psiSet H) → K)
  obtain ⟨XF, h1, h2⟩ : ∃ XF : Sp S ⟶ Xo.XF c, XF ≫ pullback.fst _ _ = X ∧
      XF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) :=
    ⟨pullback.lift X (spMap (algebraMap c.F S)) (hX.trans (GlobalTheory.DualEval.spMap_comp_ring _ _)),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hred : ∀ M : HIx Dw (psiSet H) → K, spMap (FlagTan.red c K).toRingHom ≫
      spMap (FlagTan.dir c M).toRingHom ≫ XF = frX P₀ := fun M => by
    have e : (FlagTan.red c K).toRingHom.comp (FlagTan.dir c M).toRingHom =
        (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom :=
      RingHom.ext fun a => FlagTan.fst_dir (c := c) M a
    rw [← Category.assoc, ← GlobalTheory.DualEval.spMap_comp_ring, e]
    refine GlobalTheory.FlagMod.eq_frX P₀ (by rw [Category.assoc, h1, hP]) ?_
    rw [Category.assoc, h2, ← GlobalTheory.DualEval.spMap_comp_ring]
    exact congrArg spMap (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).comp_algebraMap
  have hmem : ∀ M : HIx Dw (psiSet H) → K,
      ⊤ ≤ (spMap (FlagTan.dir c M).toRingHom ≫ XF ≫ TF.Y.j) ⁻¹ᵁ U := fun M =>
    le_preimage_of_dualNumber (FlagTan.red c K).toRingHom _ _ (by
      rw [← Category.assoc (spMap (FlagTan.dir c M).toRingHom), ← Category.assoc, hred]
      exact hU)
  refine ⟨fun k r => (ev _ U (hmem (Pi.single k 1)) r).snd, fun y' hy hs hr M hM r => ?_⟩
  have ht : FlagTan.IsTanX P₀ (y' ≫ pullback.fst _ _) := by
    refine ⟨?_, by rw [← Category.assoc, hr, GlobalTheory.FlagMod.frX_fst]⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs]
    exact (GlobalTheory.DualEval.spMap_comp_ring _ _).symm
  have e : y' = spMap (FlagTan.dir c M).toRingHom ≫ XF := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, h1]
      exact ((hk _ ht).2 M).1 hM
    · rw [Category.assoc, h2, hs, ← GlobalTheory.DualEval.spMap_comp_ring]
      exact congrArg spMap (FlagTan.dir c M).comp_algebraMap.symm
  subst e
  exact GlobalTheory.DualEval.evalPt_snd_sum (XF ≫ TF.Y.j) (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom
    (fun k => (FlagTan.dir c (Pi.single k (1 : K))).toRingHom) (FlagTan.dir c M).toRingHom M
    (fun k s => FlagTan.fst_dir (c := c) _ s) (fun s => FlagTan.fst_dir (c := c) _ s)
    (fun s => by
      refine (FlagTan.snd_dir (c := c) M s).trans (Finset.sum_congr rfl fun k _ => ?_)
      rw [mul_comm]
      refine congrArg (M k * ·) ((FlagTan.snd_dir (c := c) (Pi.single k (1 : K)) s).trans ?_).symm
      simp [Pi.single_apply]) U r (hmem M) fun k => hmem _

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTransportEquivariantCartesianPreservesCom
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvTrans

theorem epsMul_comp_algebraMap {R : Type} [CommRing R] (c : R) :
    spMap (epsMul c) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  simp only [spMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}

theorem trv_epsMul (hψ : IsPullback ψ G'.hom t.G.hom p) (g : G'.left ⟶ G'.left) {R : Type} [CommRing R]
    (q : Sp R ⟶ X) (c : R) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q (spMap (epsMul c) ≫ v) = spMap (epsMul c) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', trv_eq hψ g q (spMap (epsMul c) ≫ w) (by rw [Category.assoc, hw])
    (by rw [Category.assoc, hw', ← Category.assoc, epsMul_comp_algebraMap])]
  simp only [Category.assoc]

end GlobalTheory.EqvTrans


open MonObj GlobalTheory.EqvTrans in
theorem GlobalTheory.EqvTrans.trv_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X Y : Scheme.{0}} (t : SAB H Y) (p : X ⟶ Y) (G' : Over X) [GrpObj G'] (ψ : G'.left ⟶ t.G.left) (b : X ⟶ X) (g : G'.left ⟶ G'.left) (hG : IsGrpPullback G' t.G p ψ), IsGrpPullback G' G' b g → ∀ {R : Type} [CommRing R] (q : Sp R ⟶ X) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) (a : Fin n → R) (w : Sp (DualNumber R) ⟶ t.G.left), (∀ i, IsTanAtG t (q ≫ p) (v i)) → IsTanAtG t (q ≫ p) w → IsCombAtG t (q ≫ p) v a w → IsCombAtG t ((q ≫ b) ≫ p) (fun i => GlobalTheory.EqvTrans.trv hG.1 g q (v i)) a (GlobalTheory.EqvTrans.trv hG.1 g q w) := by
  intro E _ _ _ H X Y t p G' _ ψ b g hG hg R _ q n v a w hv _ hc
  obtain ⟨u, hu, hw⟩ := hc

  let T : Over X := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ q)
  let e1 : Over.mk (T.hom ≫ p) ⟶ tEpsG (q ≫ p) := Over.homMk (𝟙 _) (by simp [T])
  let T' : Over X := Over.mk (T.hom ≫ b)
  let e2 : Over.mk (T'.hom ≫ p) ⟶ tEpsG ((q ≫ b) ≫ p) := Over.homMk (𝟙 _) (by simp [T, T'])
  have hov : ∀ x : tEpsG (q ≫ p) ⟶ t.G,
      x.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p := fun x => by
    simpa using Over.w x

  let L : (tEpsG (q ≫ p) ⟶ t.G) → (T ⟶ G') := fun x =>
    Over.homMk (hG.1.lift x.left T.hom (by rw [hov x]; simp [T])) (hG.1.lift_snd _ _ _)
  have hL : ∀ x, (L x).left ≫ ψ = x.left := fun x => hG.1.lift_fst _ _ _
  have hLw : ∀ x, (L x).left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q := fun x => Over.w (L x)
  have hgw : g ≫ G'.hom = G'.hom ≫ b := hg.1.w

  let Φ : (tEpsG (q ≫ p) ⟶ t.G) → (tEpsG ((q ≫ b) ≫ p) ⟶ t.G) := fun x =>
    Over.homMk (trv hG.1 g q x.left) (by
      have := trv_over hG.1 g hgw q (hov x)
      simpa using this)
  have hΦ : ∀ x, (Φ x).left = (L x).left ≫ g ≫ ψ := fun x => trv_eq hG.1 g q (L x).left (hL x) (hLw x)

  let M : (tEpsG (q ≫ p) ⟶ t.G) → (T' ⟶ G') := fun x =>
    Over.homMk ((L x).left ≫ g) (by
      show ((L x).left ≫ g) ≫ G'.hom = T.hom ≫ b
      rw [Category.assoc, hgw, ← Category.assoc, Over.w])
  have hmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => by
    have h1 : ((e1 ≫ x) * (e1 ≫ y)).left = (L x * L y).left ≫ ψ :=
      hG.2 T (L x) (L y) (e1 ≫ x) (e1 ≫ y) (by simp [e1, hL]) (by simp [e1, hL])
    rw [← MonObj.comp_mul] at h1
    have h1' : (L x * L y).left ≫ ψ = (x * y).left := by rw [← h1]; simp [e1]
    have h2 : (M x * M y).left = (L x * L y).left ≫ g :=
      hg.2 T (L x) (L y) (M x) (M y) rfl rfl
    have h3 : ((e2 ≫ Φ x) * (e2 ≫ Φ y)).left = (M x * M y).left ≫ ψ :=
      hG.2 T' (M x) (M y) (e2 ≫ Φ x) (e2 ≫ Φ y) (by simp [e2, hΦ, M]) (by simp [e2, hΦ, M])
    rw [← MonObj.comp_mul, h2] at h3
    apply Over.OverMorphism.ext
    have h4 : (Φ (x * y)).left = (L x * L y).left ≫ g ≫ ψ :=
      trv_eq hG.1 g q (L x * L y).left h1' (Over.w (L x * L y))
    rw [h4, ← Category.assoc, ← h3]
    simp [e2]
  let Φm : (tEpsG (q ≫ p) ⟶ t.G) →* (tEpsG ((q ≫ b) ≫ p) ⟶ t.G) := MonoidHom.mk' Φ hmul
  refine ⟨fun i => Φ (u i), fun i => ?_, ?_⟩
  · show trv hG.1 g q (u i).left = _
    rw [hu i, trv_epsMul hG.1 g q (a i) (hv i).1]
  · have : (List.ofFn fun i => Φ (u i)) = (List.ofFn u).map Φm := by
      rw [List.map_ofFn]; rfl
    rw [this, ← map_list_prod]
    show trv hG.1 g q _ = _
    rw [hw]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGramRelationsBlocksOrthogonal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramAt

section Object

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q)

abbrev phiTP (a : Fin p) : letI := H.starRing; (pointA hv ε i X true).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T :=
  patT (T := X.A true) hv ε i (X.lin (Sum.inl a))

abbrev phiTQ (b : Fin q) : letI := H.starRing; (pointA hv ε i X false).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T :=
  patT (T := X.A false) hv ε i (X.lin (Sum.inr b))

variable [IsAlgClosed C] [CharZero C]


omit [NumberField K] in
theorem pairT_patT_gram {T T' : PAT H (Sp (𝓞 K))} {f f' : T.t.G ⟶ T'.t.G} (hf : Serre.IsLinearHom T.t.act T'.t.act f)
    (hf' : Serre.IsLinearHom T.t.act T'.t.act f') {g : 𝓞 E}
    (h : LamEq T'.t.PP.L f f' T.t.PP.L (T.t.act.act g) (𝟙 _)) : letI := H.starRing
    ∀ s t, pairT (patPoint hv ε i T').A ε (patT hv ε i hf s) (patT hv ε i hf' t) =
      pairT (patPoint hv ε i T).A ε ((patPoint hv ε i T).actT g s) t := by
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f' := hf'.isMonHom
  haveI := (patAct T).hom g
  intro s t
  have e := pairT_homT_of_lamEq (X := T.pol) (Y := T.pol) (A := T'.pol) (B := T.pol) hv ε (embO hv i) (patAct T) (patAct T)
    (patAct T') (patAct T) f f' ((patAct T).act g) (𝟙 _) h s t
  rw [homT_act, homT_id] at e
  exact e

theorem pairT_patT_orth (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) {A A' B : PAT H (Sp (𝓞 K))} {m m' : ℕ}
    (hA : HasType H A.t.act ρ m 0) (hA' : HasType H A'.t.act ρ 0 m') {f : A.t.G ⟶ B.t.G} {f' : A'.t.G ⟶ B.t.G}
    (hf : Serre.IsLinearHom A.t.act B.t.act f) (hf' : Serre.IsLinearHom A'.t.act B.t.act f') : letI := H.starRing
    ∀ s t, pairT (patPoint hv ε i B).A ε (patT hv ε i hf s) (patT hv ε i hf' t) = 0 := by
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := A.pol.A) (N := B.pol.A) f := hf.isMonHom
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := A'.pol.A) (N := B.pol.A) f' := hf'.isMonHom
  haveI : IsMonHom (1 : A'.pol.A ⟶ A.pol.A) := LamF.IsogSum.isMonHom_of_points _ fun T a b => by
    simp only [MonObj.comp_one, _root_.mul_one]
  intro s t
  have e := pairT_homT_of_lamEq (X := A.pol) (Y := A'.pol) (A := B.pol) (B := A.pol) hv ε (embO hv i) (patAct A)
    (patAct A') (patAct B) (patAct A) f f' (𝟙 _) 1 (lamEq_one hρ A A' B hA hA' hf hf') s t
  rw [homT_one, LinearMap.zero_apply, map_zero] at e
  exact e

theorem tateModule_gram_relations_blocks_orthogonal {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    letI := H.starRing
    (∀ a b s t, pairT (pointB hv ε i X).A ε (phiTP hv ε i X a s) (phiTP hv ε i X b t) =
      pairT (pointA hv ε i X true).A ε ((pointA hv ε i X true).actT (gP a b) s) t) ∧
    (∀ a b s t, pairT (pointB hv ε i X).A ε (phiTQ hv ε i X a s) (phiTQ hv ε i X b t) =
      pairT (pointA hv ε i X false).A ε ((pointA hv ε i X false).actT (gQ a b) s) t) ∧
    ∀ a b s t, pairT (pointB hv ε i X).A ε (phiTP hv ε i X a s) (phiTQ hv ε i X b t) = 0 :=
  ⟨fun a b => pairT_patT_gram (T := X.A true) hv ε i (X.lin (.inl a)) (X.lin (.inl b)) ((lamEq_of_isGram X h).1 a b),
    fun a b => pairT_patT_gram (T := X.A false) hv ε i (X.lin (.inr a)) (X.lin (.inr b)) ((lamEq_of_isGram X h).2 a b),
    fun a b => pairT_patT_orth (A := X.A true) (A' := X.A false) hv ε i X.ρ_sq X.typeP X.typeM (X.lin (.inl a))
      (X.lin (.inr b))⟩

end At

theorem exists_inverse_tateModule_sum_up_to_integer (X : CMObj H K ρ σ₁ p q) : letI := H.starRing
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime] (C : Type) [Field C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O]
      [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C),
      ∃ (ψ : Fin p → ((pointB hv ε i X).T →ₗ[ℤ_[ℓ]] (pointA hv ε i X true).T))
        (ψ' : Fin q → ((pointB hv ε i X).T →ₗ[ℤ_[ℓ]] (pointA hv ε i X false).T)),
        (∀ t, ∑ k, phiTP hv ε i X k (ψ k t) + ∑ k, phiTQ hv ε i X k (ψ' k t) = N • t) ∧
        ∀ (s : Fin p → (pointA hv ε i X true).T) (s' : Fin q → (pointA hv ε i X false).T),
          (∀ l, ψ l (∑ k, phiTP hv ε i X k (s k) + ∑ k, phiTQ hv ε i X k (s' k)) = N • s l) ∧
          ∀ l, ψ' l (∑ k, phiTP hv ε i X k (s k) + ∑ k, phiTQ hv ε i X k (s' k)) = N • s' l := by
  letI := H.starRing
  haveI hP : ∀ i, IsMonHom (M := (X.A true).pol.A) (N := X.B.pol.A) (phiP X i) := fun i => (X.lin (.inl i)).isMonHom
  haveI hQ : ∀ i, IsMonHom (M := (X.A false).pol.A) (N := X.B.pol.A) (phiQ X i) := fun i => (X.lin (.inr i)).isMonHom
  obtain ⟨N, ψ, ψ', hN, hψ, hψ', h1, h2⟩ := exists_inverse X
  exact ⟨N, hN, fun ℓ _ C _ v O _ _ hv ε i => ⟨_, _, homT_inverse (B := X.B.pol) (A := (X.A true).pol)
    (A' := (X.A false).pol) hv ε (embO hv i) (patAct X.B) (patAct (X.A true)) (patAct (X.A false)) (phiP X) (phiQ X)
    ψ ψ' h1 h2⟩⟩

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q) [IsAlgClosed C] [CharZero C]

theorem sumT_injective : letI := H.starRing
    Function.Injective fun z : (Fin p → (pointA hv ε i X true).T) × (Fin q → (pointA hv ε i X false).T) =>
      ∑ k, phiTP hv ε i X k (z.1 k) + ∑ k, phiTQ hv ε i X k (z.2 k) := by
  letI := H.starRing
  obtain ⟨N, hN, h⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', -, h2⟩ := h ℓ C v O hv ε i
  have key : ∀ (P : Point ℓ v O (𝓞 E)) (x y : P.T), N • x = N • y → x = y := fun P x y e => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], ← Nat.cast_smul_eq_nsmul ℤ_[ℓ]] at e
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hN.ne') e
  exact fun z z' e => Prod.ext
    (funext fun l => key _ _ _ (((h2 z.1 z.2).1 l).symm.trans ((congrArg (ψ l) e).trans ((h2 z'.1 z'.2).1 l))))
    (funext fun l => key _ _ _ (((h2 z.1 z.2).2 l).symm.trans ((congrArg (ψ' l) e).trans ((h2 z'.1 z'.2).2 l))))

include hv ε i in
theorem gram_det_of_emb {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ (∀ a b, H.bar (gP b a) = gP a b) ∧ ∀ a b, H.bar (gQ b a) = gQ a b := by
  letI := H.starRing
  obtain ⟨N, hN, hI⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', h1, -⟩ := hI ℓ C v O hv ε i
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X h
  have hg : ∀ b, 0 < (pointA hv ε i X b).A.g := fun b => (dims X).2.2.trans_eq ((dims X).1 b).symm
  have hi := sumT_injective hv ε i X
  refine ⟨det_ne_zero_of_inverse hN (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
      (hg true) (phiTP hv ε i X) (phiTQ hv ε i X) gP hP hO (fun t => ⟨_, _, h1 t⟩) fun s hs => ?_,
    det_ne_zero_of_inverse hN (A := pointA hv ε i X false) (A' := pointA hv ε i X true) (B := pointB hv ε i X)
      (hg false) (phiTQ hv ε i X) (phiTP hv ε i X) gQ hQ (fun a b s t => ?_)
      (fun t => ⟨_, _, (add_comm _ _).trans (h1 t)⟩) fun s hs => ?_,
    star_gram (A := pointA hv ε i X true) (B := pointB hv ε i X) (hg true) (phiTP hv ε i X) gP hP,
    star_gram (A := pointA hv ε i X false) (B := pointB hv ε i X) (hg false) (phiTQ hv ε i X) gQ hQ⟩
  · exact congrArg Prod.fst (@hi (s, 0) (0, 0) (by simp only [hs, Pi.zero_apply, map_zero, Finset.sum_const_zero]))
  · exact ((isAlt_pairT (pointB hv ε i X).A ε).neg_eq _ _).symm.trans (neg_eq_zero.2 (hO b a t s))
  · exact congrArg Prod.snd (@hi (0, s) (0, 0) (by simp only [hs, Pi.zero_apply, map_zero, Finset.sum_const_zero]))

variable [Algebra ℤ_[ℓ] C]

theorem gram_V {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    letI := H.starRing
    (∀ a b x y, (pointB hv ε i X).pairV (phiVP hv ε i X a x) (phiVP hv ε i X b y) =
      (pointA hv ε i X true).pairV ((pointA hv ε i X true).actV (gP a b) x) y) ∧
    (∀ a b x y, (pointB hv ε i X).pairV (phiVQ hv ε i X a x) (phiVQ hv ε i X b y) =
      (pointA hv ε i X false).pairV ((pointA hv ε i X false).actV (gQ a b) x) y) ∧
    ∀ a b x y, (pointB hv ε i X).pairV (phiVP hv ε i X a x) (phiVQ hv ε i X b y) = 0 := by
  letI := H.starRing
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X h
  refine ⟨fun a b x y => ?_, fun a b x y => ?_, fun a b x y => ?_⟩
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointA hv ε i X true) (g₂ := LinearMap.id) (hP a b) x y
    rw [LinearMap.baseChange_id] at e
    exact e
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointA hv ε i X false) (g₂ := LinearMap.id) (hQ a b) x y
    rw [LinearMap.baseChange_id] at e
    exact e
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointB hv ε i X) (g₁ := 0) (g₂ := 0)
      (fun s t => (hO a b s t).trans (map_zero _).symm) x y
    rw [LinearMap.baseChange_zero, LinearMap.baseChange_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero] at e
    exact e

end At

theorem gram_det (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)}
    (h : IsGram X gP gQ) :
    gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ (∀ a b, H.bar (gP b a) = gP a b) ∧ ∀ a b, H.bar (gQ b a) = gQ a b := by
  obtain ⟨ε⟩ : Nonempty (Eps 2 ℂ_[2]) := inferInstance
  exact gram_det_of_emb (PadicComplexInt.integers 2) ε (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[2])).toRingHom X h

end Object

end GlobalTheory.GramAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermsumTrFacDifferentiable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem termsum_fderiv_mul_affine {g : ℕ} (f F : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f) (hF : Differentiable ℂ F)
    (c : ℂ) (p W : Fin g → ℂ) :
    fderiv ℂ (fun Z => f Z * F (c • Z + p)) 0 W = fderiv ℂ f 0 W * F p + f 0 * fderiv ℂ F p (c • W) := by
  have h1 : HasFDerivAt (fun Z : Fin g → ℂ => c • Z + p) (c • ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 :=
    ((hasFDerivAt_id (0 : Fin g → ℂ)).const_smul c).add_const p
  have h2 : HasFDerivAt F (fderiv ℂ F p) (c • (0 : Fin g → ℂ) + p) := by
    rw [smul_zero, zero_add]; exact (hF p).hasFDerivAt
  have h3 : HasFDerivAt (fun Z => F (c • Z + p)) _ 0 := h2.comp (0 : Fin g → ℂ) h1
  have h4 : HasFDerivAt (fun Z => f Z * F (c • Z + p)) _ 0 := (hf 0).hasFDerivAt.mul h3
  rw [h4.fderiv]
  simp
  ring

theorem termsum_trFac_differentiable {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ)
    (M N : Fin g → ℤ) : Differentiable ℂ (trFac τ a b m M N) := by
  unfold trFac
  simp only [dotProduct]
  fun_prop

theorem termsum_full_isSymm {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (hS : S.IsSymm) : (d.full σ S).IsSymm := by
  unfold CD.full
  apply Matrix.IsSymm.submatrix
  exact Matrix.IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hS)

theorem termsum_half_aF {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) : Half (d.aF σ) := by
  intro j
  unfold CD.aF
  rcases σ j with i | l
  · exact d.ha i
  · exact Or.inl rfl

theorem termsum_half_bF {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) : Half (d.bF σ) := by
  intro j
  unfold CD.bF
  rcases σ j with i | l
  · exact d.hb i
  · exact d.hb2 l

theorem term_sum_and_fderiv : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → ∀ (m : ℕ) (M Nn : Fin g → ℤ) (W : Fin g → ℂ), (Summable fun χ => ‖d.term σ S m M Nn χ 0‖) ∧ (Summable fun χ => ‖fderiv ℂ (d.term σ S m M Nn χ) 0 W‖) ∧ ∑' χ, d.term σ S m M Nn χ 0 = trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn 0 ∧ ∑' χ, fderiv ℂ (d.term σ S m M Nn χ) 0 W = fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn) 0 W := by
  intro N g' r g bX d σ S hS hpos m M Nn W
  have hθ := (_root_.GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy g _ _ _ (termsum_full_isSymm d σ S hS) hpos (termsum_half_aF d σ) (termsum_half_bF d σ)).1
  set p := (m : ℂ)⁻¹ • perV (d.full σ S) M Nn with hp
  obtain ⟨hs, he⟩ := _root_.GlobalTheory.MBLow.Cl.fj_expansion N g' r g bX d σ S hS hpos p
  obtain ⟨hd, hD⟩ := _root_.GlobalTheory.MBLow.Cl.fj_expansion_fderiv N g' r g bX d σ S hS hpos
  obtain ⟨hs', he'⟩ := hD p ((m : ℂ) • W)
  have hf := termsum_trFac_differentiable (d.full σ S) (d.aF σ) (d.bF σ) m M Nn
  set f := trFac (d.full σ S) (d.aF σ) (d.bF σ) m M Nn with hfdef
  have e0 : ∀ χ, d.term σ S m M Nn χ 0 = f 0 * d.fj σ S χ p := fun χ => by
    simp only [CD.term, smul_zero, zero_add, hfdef, hp]
  have e1 : ∀ χ, fderiv ℂ (d.term σ S m M Nn χ) 0 W =
      fderiv ℂ f 0 W * d.fj σ S χ p + f 0 * fderiv ℂ (d.fj σ S χ) p ((m : ℂ) • W) := fun χ =>
    termsum_fderiv_mul_affine f (d.fj σ S χ) hf (hd χ) m p W
  have e2 : fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn) 0 W = _ :=
    termsum_fderiv_mul_affine f _ hf hθ m p W
  have s1 := hs.of_norm
  have s2 := hs'.of_norm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [e0]
    exact (s1.mul_left _).norm
  · simp only [e1]
    exact ((s1.mul_left _).add (s2.mul_left _)).norm
  · simp only [e0]
    rw [tsum_mul_left, he]
    simp only [trF, smul_zero, zero_add, hfdef, hp]
  · simp only [e1]
    rw [(s1.mul_left _).tsum_add (s2.mul_left _), tsum_mul_left, tsum_mul_left, he, he', e2]

end GlobalTheory.MBLow.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicProperties
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThKBasic

theorem thetaBasic : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ThetaBasic := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hS := hP.weil.isUSplitting
  obtain ⟨l, hl, hlt⟩ := _root_.GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact F (Fin n × Fin d)
  refine ⟨fun Φ hΦ => ⟨?_, ?_, _root_.GlobalTheory.ThetaModGrowthPair.theta_modGrowth hKP F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ⟩, ?_⟩
  · refine (hS.cont l hl Φ hΦ).congr fun x => ?_
    simp only [theta]
    exact hlt _ (hS.pres _ _ hΦ)
  · intro γ hγ γ' hγ' g h
    simp only [theta]
    have e : om (γ * g, γ' * h) Φ = om (γ, γ') (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul]; rfl
    rw [e]
    exact _root_.GlobalTheory.ThetaRatPair.thetaSum_om_rat hKP F E σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' _ (hS.pres _ _ hΦ)
  · intro φ hφ g h
    obtain ⟨T, hT⟩ := hS.adm (g, h) l hl φ hφ
    refine T.continuous.congr fun f => ?_
    simp only [theta]
    have hm : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) φ ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    rw [← hlt _ (hS.pres _ _ hm)]
    exact (hT f).symm

end GlobalTheory.ThKBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadingsStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationLaws_centralMovedReadings : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G), (∀ i σ, w i σ ∈ Subgroup.center G) → R.LUnif → (moveR R w).LUnif := by
  first | exact @GlobalTheory.Unframe.lUnif_moveR | exact GlobalTheory.Unframe.lUnif_moveR | (intros; apply GlobalTheory.Unframe.lUnif_moveR <;> assumption)
end

