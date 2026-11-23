module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPtAppLEOfComp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.CompHS GlobalTheory.CxPts GlobalTheory.Vanishing
open GlobalTheory.TangentOrigin GlobalTheory.CechPic GlobalTheory.TopForm GlobalTheory.Adelic

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y}
  {Z : Comp Xo c}

theorem evalPt_appLE_of_comp {R : Type} [CommRing R] {A B : Scheme.{0}} (v : Sp R ⟶ A) (φ : A ⟶ B) (U : B.Opens)
    (V : A.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(B, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV (φ.appLE U V e f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem canId_val_mul_det (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (ω : CanId M)
    {L : Type} [Field L] [iL : Algebra c.F L] (Q : FrPt Xo c L)
    (v : GlobalTheory.FlagTan.TIx Dw (GlobalTheory.FlagTan.psiSet H) → FrPt Xo c (DualNumber L))
    (hv : GlobalTheory.FlagTan.IsTanFrame (GlobalTheory.FlagTan.psiSet H) Q v) (z : Sp L ⟶ M.X)
    (zv : GlobalTheory.FlagTan.TIx Dw (GlobalTheory.FlagTan.psiSet H) → (Sp (DualNumber L) ⟶ M.X)) (i : M.K.bundle.ι) (k : X.F.J)
    (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i) (g : Fin (GlobalTheory.FlagTan.dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O)
    (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O) (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k))
    (hQ : X.F.ChartFr k (z ≫ toFlag M) hk Q) (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) :
    H0.val (B := LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω.ω *
        (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      evalPt z O hz (M.K.jacobian i hO g) := by
  have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).1 Q
  have a := ω.isKS L Q Q 1 v z zv i k O hO g hz hzv hk ho hi hQ hb hv hl
  simpa only [Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, one_mul] using a

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasis
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.FlagBasis

theorem exists_coeff {C U : Type} [Field C] [AddCommGroup U] [Module C U] {n : ℕ} (b : Fin n → U) (i : ℕ)
    {y : U} (hy : y ∈ step C b i) : ∃ r : Fin n → C, (∀ j : Fin n, i ≤ j → r j = 0) ∧ ∑ j, r j • b j = y := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Pi.single k 1, fun j hj => Pi.single_eq_of_ne ?_ _, by simp [Pi.single_apply]⟩
    rintro rfl
    exact absurd hk (not_lt.2 hj)
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r + s, fun j hj => by simp [hr j hj, hs j hj], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨a • r, fun j hj => by simp [hr j hj], by simp [Finset.smul_sum, smul_smul]⟩

theorem exists_lift {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U]
    [IsScalarTower O C U] {v : Valuation C ℝ≥0} (hv : v.Integers O) {n : ℕ} {La : Submodule O U} (hfg : La.FG)
    {b : Fin n → U} (hb : LinearIndependent C b) (i : Fin n) {a : C} (ha : a ≠ 0) (hLa : a • b i ∈ La) :
    ∃ (w : U) (c : C), c ≠ 0 ∧ w ∈ La ∧ w - c • b i ∈ step C b i ∧
      ∀ x ∈ La, x ∈ step C b (i + 1) → ∃ o : O, x - o • w ∈ step C b i := by
  obtain ⟨c, hc, e, -⟩ := exists_grAt_eq hv hfg b i (hb.notMem_span_image (by simp)) ha
    (Submodule.zero_mem _) (by rwa [add_zero])
  obtain ⟨w, hw, hw'⟩ : c • (step C b i).mkQ (b i) ∈ grAt C La b i :=
    e ▸ Submodule.mem_span_singleton_self _
  have hw'' : (step C b i).mkQ w = c • (step C b i).mkQ (b i) := hw'
  refine ⟨w, c, hc, hw.1, (Submodule.Quotient.eq _).1 hw'', fun x hx hx' => ?_⟩
  have h1 : (step C b i).mkQ x ∈ grAt C La b i := ⟨x, ⟨hx, hx'⟩, rfl⟩
  rw [e, ← hw''] at h1
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 h1
  exact ⟨o, (Submodule.Quotient.eq _).1 ho.symm⟩

theorem exists_adapted_basis : ∀ (O C U : Type) [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] (v : Valuation C ℝ≥0), v.Integers O → ∀ (n : ℕ) (La : Submodule O U), La.FG → ∀ b : Fin n → U, LinearIndependent C b → (∀ j, ∃ a : C, a ≠ 0 ∧ a • b j ∈ La) → ∃ g : Matrix (Fin n) (Fin n) C, (∀ i j, i < j → g i j = 0) ∧ (∀ i, g i i ≠ 0) ∧ IsLatBasis C La fun i => ∑ j, g i j • b j := by
  intro O C U _ _ _ _ _ _ _ v hv n La hfg b hb hLa
  classical
  choose a ha hLa using hLa
  choose w c hc hw hwb hgen using fun i => exists_lift hv hfg hb i (ha i) (hLa i)
  choose r hr hrb using fun i => exists_coeff b _ (hwb i)
  let g : Matrix (Fin n) (Fin n) C := fun i j => r i j + if j = i then c i else 0
  have hg : ∀ i j, i < j → g i j = 0 := fun i j h => by
    simp [g, hr i j h.le, h.ne']
  have hd : ∀ i, g i i ≠ 0 := fun i => by simpa [g, hr i i le_rfl] using hc i
  have hgw : (fun i => ∑ j, g i j • b j) = w := funext fun i => by
    simp [g, add_smul, Finset.sum_add_distrib, hrb]
  have hws : ∀ i : Fin n, w i ∈ step C b (i + 1) := fun i => by
    simpa using Submodule.add_mem _ (step_mono b (Nat.le_succ _) (hwb i))
      (Submodule.smul_mem _ (c i) (mem_step_succ b i))
  refine ⟨g, hg, hd, ?_, ?_⟩
  · have hu : IsUnit g := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isLowerTriangular _ fun i j hij => hg i j hij]
      exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
    exact (Matrix.linearIndependent_rows_iff_isUnit.2 hu).map' (Fintype.linearCombination C b)
      (LinearMap.ker_eq_bot.2 fun s t h => funext (Fintype.linearIndependent_iffₛ.1 hb s t h))
  · rw [hgw]
    refine le_antisymm (le_inf (Submodule.span_le.2 (Set.range_subset_iff.2 hw))
      (Submodule.span_le_restrictScalars O C _)) ?_
    have key : ∀ k, k ≤ n → ∀ x ∈ La, x ∈ step C b k → x ∈ Submodule.span O (Set.range w) := by
      intro k
      induction k with
      | zero =>
        intro _ x _ hx
        rw [step_zero, Submodule.mem_bot] at hx
        exact hx ▸ Submodule.zero_mem _
      | succ k ih =>
        intro hk x hx hx'
        obtain ⟨o, ho⟩ := hgen ⟨k, hk⟩ x hx hx'
        have h1 := ih (Nat.le_of_succ_le hk) _ (La.sub_mem hx (La.smul_mem o (hw _))) ho
        simpa using Submodule.add_mem _ h1
          (Submodule.smul_mem _ o (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩))
    rintro x ⟨hx, hx'⟩
    exact key n le_rfl x hx (Submodule.span_le.2 (Set.range_subset_iff.2 fun i =>
      step_mono b (Nat.succ_le_of_lt i.2) (hws i)) hx')

end GlobalTheory.CompHt.FlagBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverWithDualNumberDerivations
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem exists_basis_kaehler_D {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension D k A] :
    ∃ (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k]), ∀ i, B i = KaehlerDifferential.D k A (f i) := by
  classical
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨fun i => P.val (e.symm i), P.basisKaehler.reindex e, fun i => by simp⟩

def derivHom {k A : Type} [CommRing k] [CommRing A] [Algebra k A] (δ : Derivation k A A) :
    A →+* DualNumber A where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (δ s)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, smul_eq_mul, mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [add_comm, add_left_comm, add_assoc]

theorem snd_eq_sum_of_basis {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k]) (hB : ∀ i, B i = KaehlerDifferential.D k A (f i))
    {K : Type} [Field K] (θ : A →+* DualNumber K) (h : ∀ a, (θ (algebraMap k A a)).snd = 0) (s : A) :
    (θ s).snd = ∑ b, (θ (f b)).snd *
      (θ (((B.coord b).compDer (KaehlerDifferential.D k A)) s)).fst := by
  first
  | exact @_root_.GlobalTheory.SecondComponentSum.snd_eq_sum
  | exact _root_.GlobalTheory.SecondComponentSum.snd_eq_sum
  | (apply _root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SecondComponentSum.snd_eq_sum ..)

theorem snd_eq_zero_of_isAlgebraic {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K]
    (φ : F →+* DualNumber K) (a : F) : (φ a).snd = 0 := by
  letI : Algebra ℚ (DualNumber K) := (φ.comp (algebraMap ℚ F)).toAlgebra
  have : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  have := Algebra.FormallyUnramified.ext' (R := ℚ) (A := F) (B := DualNumber K)
    (TrivSqZeroExt.fstHom K K K).toRingHom ⟨2, TrivSqZeroExt.kerIdeal_sq K K⟩ φ.toRatAlgHom
    ((algebraMap K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).toRingHom.comp φ)).toRatAlgHom
    (fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  have e := DFunLike.congr_fun this a
  change φ a = _ at e
  rw [e]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}

theorem exists_derivFrame (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (W : M.X.Opens) (p : M.X)
    (hp : p ∈ W) : ∃ (W' : M.X.Opens) (_ : IsAffineOpen W')
      (d : Fin (dimFlag Dw) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))), p ∈ W' ∧ W' ≤ W ∧
      (∀ b s, (d b s).fst = s) ∧
      ∀ (K : Type) [Field K] (θ : Γ(M.X, W') →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s,
        (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd) := by
  obtain ⟨V, hV, hx, hVW⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens hp
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension (dimFlag Dw)) M.str M.smooth
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(M.X, V)), p ∈ M.X.basicOpen (t : Γ(M.X, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(M.X, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str (M.X.basicOpen (t : Γ(M.X, V)))).IsStandardSmoothOfRelativeDimension
      (dimFlag Dw) := by
    rw [← resG_comp_algX M.str (M.X.basicOpen_le (t : Γ(M.X, V)))]
    exact h₁
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str (M.X.basicOpen (t : Γ(M.X, V)))).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension (dimFlag Dw) c.F Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))) := h₂
  obtain ⟨f, B, hB⟩ := exists_basis_kaehler_D (D := dimFlag Dw) (k := c.F) (A := Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))))
  refine ⟨_, IsAffineOpen.basicOpen hV _, fun b => derivHom ((B.coord b).compDer (KaehlerDifferential.D c.F _)),
    hxt, (M.X.basicOpen_le _).trans (hVW.trans le_rfl), fun b s => by simp [derivHom], fun K _ θ =>
    ⟨fun b => (θ (f b)).snd, fun s => ?_⟩⟩
  rw [snd_eq_sum_of_basis f B hB θ (fun a => snd_eq_zero_of_isAlgebraic (θ.comp (algebraMap c.F _)) a) s]
  simp [derivHom]

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesFramesStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  first | exact @GlobalTheory.ArchCoords.exists_coords | exact GlobalTheory.ArchCoords.exists_coords | (intros; apply GlobalTheory.ArchCoords.exists_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesPlaceSignaStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_placeSignatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  first | exact @GlobalTheory.ArchCoordsD.exists_coords | exact GlobalTheory.ArchCoordsD.exists_coords | (intros; apply GlobalTheory.ArchCoordsD.exists_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedLocusHomogeneousEquationsSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus

open GlobalTheory.AbLaw in
theorem germ_eq {Rg : Type} [CommRing Rg] {A₀ T X : Scheme.{0}} {f : A₀ ⟶ Sp Rg} {N : LB A₀} {mA mB : ℕ}
    (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N)
    (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T)
    (hw : φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg) (hF : F.IsHomogeneous d)
    (z : X) (i : (Q d).I) (hz : φ z ∈ (Q d).W i) :
    MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z ((Q d).ch i)) F =
      ∑ k, gs p z ⊤ (ringOf g (polys Q a d F k)) * gs φ z ((Q d).W i) ((Q d).u k i) := by
  have hq : φ z ∈ N.U ((Q d).ch i) := (Q d).le i hz
  have hψ : ∀ x : Γ(T, ⊤), gs p z ⊤ x =
      ((X.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp (p.app ⊤).hom) x := fun x => gs_eq p z ⊤ trivial x
  rw [GlobalTheory.T.germ_form_pulledBack_combinations_expand_monomials Rg A₀ T X f N mA mB a g φ p hw d F hF z _ hq]
  have hv : ∀ ν, gs φ z (N.U ((Q d).ch i)) ((monSec a d ν).f ((Q d).ch i)) =
      ∑ k, gs p z ⊤ (ringOf g (MvPolynomial.C (vecOf (Q d) (monSec a d ν) k))) * gs φ z ((Q d).W i) ((Q d).u k i) := by
    intro ν
    exact (GlobalTheory.T.section_local_expansion Rg A₀ X f _ (Q d) (monSec a d ν) φ z i hz).trans
      (Finset.sum_congr rfl fun k _ => by rw [GlobalTheory.T.germ_constants_eq_along_affineSpace_square Rg A₀ T X f (mA * mB) g φ p hw z])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hv, polys, hψ, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun ν _ => by ring

theorem exists_closed_formsOK : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A₀ B₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H), Flat f → GlobalTheory.AbLaw.IsProjBy f → N.IsLB → ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  intro Rg _ _ A₀ B₀ f fB N H mA mB a b hf hp hN
  have Q : ∀ d : ℕ, GlobalTheory.AbLaw.Perf f (GlobalTheory.AbLaw.pw N (d : ℤ)) := fun d =>
    (GlobalTheory.AbLaw.nonempty_perf_of_noetherian Rg A₀ f hf hp _ (GlobalTheory.AbLaw.isLB_pw hN d)).some
  refine ⟨Sp (MvPolynomial (Fin (mA * mB)) Rg ⧸ formIdeal Q a fB b),
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (formIdeal Q a fB b))),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  intro T X' g φ p hpb
  rw [GlobalTheory.T.factors_through_zero_locus]
  have hmem : ∀ d (z : X'), ∃ i, φ z ∈ (Q d).W i := fun d z =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [(Q d).cover]; trivial)
  constructor
  · intro hF
    have hle : formIdeal Q a fB b ≤ RingHom.ker (ringOf g) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨d, F, k, hFh, hK, rfl⟩
      have := GlobalTheory.T.eq_zero_of_differential_kernel_zero_germs Rg A₀ T X' f _ (Q d) (g ≫ affπ Rg (mA * mB)) φ p hpb
        (fun k => ringOf g (polys Q a d F k)) (GlobalTheory.T.coordinatePolynomials_form_mem_kernel_differential Rg A₀ T f N mA mB Q a g d F) (fun z i hz => by
          rw [← germ_eq Q a g φ p hpb.w d F hFh z i hz]
          exact hF d F hFh hK z ((Q d).ch i) ((Q d).le i hz))
      exact congrFun this k
    exact fun P hP => hle hP
  · intro h d F hFh hK z q hq
    obtain ⟨i, hi⟩ := hmem d z
    rw [GlobalTheory.T.homogeneousForm_vanishing_combination_chart_indep Rg A₀ T X' N mA mB a φ p _ (matOf g) d F hFh z q ((Q d).ch i) hq ((Q d).le i hi),
      germ_eq Q a g φ p hpb.w d F hFh z i hi]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [h _ (Ideal.subset_span ⟨d, F, k, hFh, hK, rfl⟩), gs_eq p z ⊤ trivial, map_zero, map_zero, zero_mul]

end GlobalTheory.FormsLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceHeckeCharacterBoundedLevelTrivia
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.HeckeCont

open Formalism.L2.Host GlobalTheory.Mem.Col2.SplitChar

theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem eq_one_of_cong : ∀ (D : D7) (χ : HChar D.host.E) (S : Finset ℕ) (k : ℕ), (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1 := by
  intro D χ S k hS hv
  refine ⟨(∏ q ∈ S, q) ^ k, pow_pos (Finset.prod_pos fun q hq => (hS q hq).pos) k, ?_⟩
  rintro u hu ⟨s, hs, e⟩
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local _ χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu) (fun w => ?_) (fun v x hx => ?_)
  · rw [finIdl_fst]
    rfl
  · have hU : Valued.v ((finIdl D u : AdeleRing (𝓞 D.host.E) D.host.E).2 v) = 1 := finIdl_unit hu v
    have hxU : IsUnitAt v x := by
      show Valued.v (x : v.adicCompletion D.host.E) = 1
      rw [hx]
      exact hU
    rcases hv v with hunr | ⟨q, hq, hov, hlev⟩
    · exact hunr x hxU
    · refine hlev x hxU ?_
      rw [hx, vl_sub_one, e]
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
      have hP : OverP D.host (∏ q ∈ S, q) v := by
        show (((∏ q ∈ S, q : ℕ)) : 𝓞 D.host.E) ∈ v.asIdeal
        rw [hc, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hov
      have h1 := le_exp_neg_one_of_lt_one (val_nat_lt hP)
      rw [map_mul, Nat.cast_pow, map_pow]
      calc vl D v ((∏ q ∈ S, q : ℕ) : AE D) ^ k * vl D v s ≤ vl D v ((∏ q ∈ S, q : ℕ) : AE D) ^ k :=
            mul_le_of_le_one_right' (vl_le hs v)
        _ ≤ WithZero.exp (-1 : ℤ) ^ k := pow_le_pow_left₀ zero_le' h1 k
        _ = WithZero.exp (-(k : ℤ)) := by rw [← WithZero.exp_nsmul]; congr 1; simp

end GlobalTheory.HeckeCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompleteDvrEmbedding

theorem exists_injective_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal) (hv : v.Integers O)
    [Algebra A B] [Algebra.IsIntegral A B] (hφ : Function.Injective (algebraMap A B)) (j : A →+* O)
    (hj : Function.Injective ((algebraMap O C).comp j)) :
    ∃ j' : B →+* O, Function.Injective ((algebraMap O C).comp j') := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_14 h_15; revert A B O C h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 v hv h_14 h_15 hφ j hj; exact @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral)
  | exact @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral
  | exact _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral
  | (apply _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral ..)

theorem exists_embedding_padicComplexInt :
    ∀ T : CDVR, T.FinRes → ∃ (p : ℕ) (_ : Fact p.Prime) (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p]), ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a) := by
  intro T hT
  haveI : Finite (IsLocalRing.ResidueField T.V) := hT
  obtain ⟨p, hp, _, hfin⟩ := GlobalTheory.exists_padicInt_algebra_finite T.V
  have hinj : Function.Injective (algebraMap ℤ_[p] T.V) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0
      (PadicInt.irreducible_p (p := p))
    rw [map_mul, map_pow, map_natCast] at ha
    exact mul_ne_zero (u.isUnit.map _).ne_zero
      (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) ha
  have hj : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (padicIntHom p)) :=
    (algebraMap ℚ_[p] ℂ_[p]).injective.comp Subtype.val_injective
  obtain ⟨kO, hkO⟩ := exists_injective_of_integral _ (PadicComplexInt.integers p) hinj (padicIntHom p) hj
  exact ⟨p, hp, IsFractionRing.lift (K := T.Fr) hkO, kO, fun a => (IsFractionRing.lift_algebraMap hkO a).symm⟩

end GlobalTheory.CompleteDvrEmbedding
end

