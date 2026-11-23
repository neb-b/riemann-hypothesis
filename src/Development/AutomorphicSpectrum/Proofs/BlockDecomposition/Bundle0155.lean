module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0150
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0105
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvFGExact
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u

namespace GlobalTheory.CompanionTheory.CosieveBC

open GlobalTheory.CompanionTheory.CosieveMV

section Cochains

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

abbrev cw (W : ObjectProperty C) : Cx.{max u v w} R := CH.cx (W.ι ⋙ F)

abbrev supP (U V : ObjectProperty C) : ObjectProperty C := fun T => U T ∨ V T

abbrev infP (U V : ObjectProperty C) : ObjectProperty C := fun T => U T ∧ V T

variable {U V : ObjectProperty C}

theorem le_supL : U ≤ supP U V := fun _ h => Or.inl h
theorem le_supR : V ≤ supP U V := fun _ h => Or.inr h
theorem inf_leL : infP U V ≤ U := fun _ h => h.1
theorem inf_leR : infP U V ≤ V := fun _ h => h.2

def liftW {W P : ObjectProperty C} (hP : Cosieve P) {n : ℕ} (t : ComposableArrows W.FullSubcategory n)
    (h : P (t.obj 0).obj) : ComposableArrows P.FullSubcategory n :=
  liftCh hP (t ⋙ W.ι) h

variable (U V)

def mvF : Cx.Hom (cw F (supP U V)) (prodCx (cw F U) (cw F V)) (RingHom.id R) where
  f n := LinearMap.prod ((resU F le_supL).pullC n) ((resU F le_supR).pullC n)
  comm n x := Prod.ext ((resU F le_supL).d_pullC n x) ((resU F le_supR).d_pullC n x)

def mvG : Cx.Hom (prodCx (cw F U) (cw F V)) (cw F (infP U V)) (RingHom.id R) where
  f n := ((resU F inf_leL).pullC n).comp (LinearMap.fst R _ _) - ((resU F inf_leR).pullC n).comp (LinearMap.snd R _ _)
  comm n x := by
    change CH.d _ n ((resU F inf_leL).pullC n x.1 - (resU F inf_leR).pullC n x.2) =
      (resU F inf_leL).pullC (n + 1) (CH.d _ n x.1) - (resU F inf_leR).pullC (n + 1) (CH.d _ n x.2)
    rw [map_sub, (resU F inf_leL).d_pullC, (resU F inf_leR).d_pullC]

variable {U V}

theorem mvF_inj (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Injective ((mvF F U V).f n) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  funext t
  rcases (t.obj 0).property with h | h
  · exact congrFun (congrArg Prod.fst hx) (liftW hU t h)
  · exact congrFun (congrArg Prod.snd hx) (liftW hV t h)

open Classical in
theorem mvFG_exact (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Exact ((mvF F U V).f n) ((mvG F U V).f n) := by
  intro y
  constructor
  · intro hy
    obtain ⟨a, b⟩ := y
    have hab : ∀ s : ComposableArrows (infP U V).FullSubcategory n,
        (resU F inf_leL).pullC n a s = (resU F inf_leR).pullC n b s := fun s =>
      sub_eq_zero.1 (congrFun hy s)
    refine ⟨fun t => if h : U (t.obj 0).obj then a (liftW hU t h) else
      b (liftW hV t ((t.obj 0).property.resolve_left h)), Prod.ext ?_ ?_⟩
    · funext s
      exact dif_pos (s.obj 0).property
    · funext s
      by_cases h : U (s.obj 0).obj
      · refine (dif_pos h).trans ?_
        exact hab (liftW (P := infP U V) (fun _ _ f h => ⟨hU f h.1, hV f h.2⟩) s ⟨h, (s.obj 0).property⟩)
      · exact dif_neg h
  · rintro ⟨x, rfl⟩
    refine sub_eq_zero.2 ?_
    rfl


open Classical in
def extV (hU : Cosieve U) (hV : Cosieve V) {n : ℕ} (y : CH.Cn ((infP U V).ι ⋙ F) n) : CH.Cn (U.ι ⋙ F) n :=
  fun t => if h : V (t.obj 0).obj then
    y (liftW (P := infP U V) (fun _ _ f h => ⟨hU f h.1, hV f h.2⟩) t ⟨(t.obj 0).property, h⟩) else 0

theorem mvG_surj (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Surjective ((mvG F U V).f n) := by
  intro y
  refine ⟨(extV F hU hV y, 0), funext fun s => ?_⟩
  have e1 : (resU F inf_leL).pullC n (extV F hU hV y) s = y s := dif_pos (s.obj 0).property.2
  have e2 : (resU F inf_leR).pullC n (0 : CH.Cn (V.ι ⋙ F) n) s = 0 := congrFun (map_zero _) s
  change (resU F inf_leL).pullC n (extV F hU hV y) s - (resU F inf_leR).pullC n (0 : CH.Cn (V.ι ⋙ F) n) s = y s
  rw [e1, e2, sub_zero]

end Cochains

section Family

universe w' v' u'

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] (G : C' ⥤ C) {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)] (F : ι → (C ⥤ ModuleCat.{w} R)) (F' : C' ⥤ ModuleCat.{w'} R')
  (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T)
  (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x, τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))

def Phi {W : ObjectProperty C} {W' : ObjectProperty C'} (h : ∀ T, W' T → W (G.obj T)) (i : ι) (n : N i) :
    Cx.Hom (cw (F i) W) (cw F' W') σ :=
  (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) h).hom

variable {G F F' τ hτ}

theorem phi_lin (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x) {W : ObjectProperty C} {W' : ObjectProperty C'}
    (h : ∀ T, W' T → W (G.obj T)) : Lin (Phi G F F' τ hτ h) :=
  ⟨fun i n n' k x => funext fun s => hadd i n n' _ _, fun i r n k x => funext fun s => hsm i r n _ _⟩

theorem lin_prod {K L : ι → Cx.{w} R} {K' L' : Cx.{w'} R'} {φ : ∀ i, N i → Cx.Hom (K i) K' σ}
    {ψ : ∀ i, N i → Cx.Hom (L i) L' σ} (hφ : Lin φ) (hψ : Lin ψ) : Lin fun i n => prodHom (φ i n) (ψ i n) :=
  ⟨fun i n n' k x => Prod.ext (hφ.1 i n n' k x.1) (hψ.1 i n n' k x.2),
    fun i r n k x => Prod.ext (hφ.2 i r n k x.1) (hψ.2 i r n k x.2)⟩

theorem bc_sup [Fintype ι] [DecidableEq ι] [∀ i, Module.Flat R (N i)]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x) {U V : ObjectProperty C} {U' V' : ObjectProperty C'}
    (hU : Cosieve U) (hV : Cosieve V) (hU' : Cosieve U') (hV' : Cosieve V')
    (hu : ∀ T, U' T → U (G.obj T)) (hv : ∀ T, V' T → V (G.obj T))
    (tU : BC (Phi G F F' τ hτ hu)) (tV : BC (Phi G F F' τ hτ hv))
    (tI : BC (Phi G F F' τ hτ (W := infP U V) (W' := infP U' V') fun T h => ⟨hu T h.1, hv T h.2⟩)) :
    BC (Phi G F F' τ hτ (W := supP U V) (W' := supP U' V') fun T h => h.imp (hu T) (hv T)) := by
  refine (bc_ses (fun i => mvF (F i) U V) (fun i => mvG (F i) U V) (mvF F' U' V') (mvG F' U' V')
    (fun i n => mvF_inj _ hU hV n) (fun i n => mvFG_exact _ hU hV n) (fun i n => mvG_surj _ hU hV n)
    (fun n => mvF_inj _ hU' hV' n) (fun n => mvFG_exact _ hU' hV' n) (fun n => mvG_surj _ hU' hV' n)
    _ (fun i n => prodHom (Phi G F F' τ hτ hu i n) (Phi G F F' τ hτ hv i n)) _
    (phi_lin hadd hsm _) (lin_prod (phi_lin hadd hsm _) (phi_lin hadd hsm _)) (phi_lin hadd hsm _)
    ?_ ?_).1 (bc_prod _ _ (phi_lin hadd hsm _) (phi_lin hadd hsm _) tU tV) tI
  · exact fun i m k x => rfl
  · intro i m k x
    funext s
    exact map_sub (τ i m _) _ _

end Family

end GlobalTheory.CompanionTheory.CosieveBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExists
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.MassTest

theorem exists_bump {W : Type} [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W] [MeasurableSpace W]
    [BorelSpace W] (ν : Measure W) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {U : Set W}
    (hU : IsOpen U) {x : W} (hx : x ∈ U) :
    ∃ φ : W → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧ tsupport φ ⊆ U ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂ν ≠ 0 ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂ν ≠ ⊤ := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨f, hf1, hf0, hfc, hfr⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := x))
    (isOpen_interior (s := K)).isClosed_compl (by simpa using hxK)
  have hsupp : Function.support f ⊆ K := by
    intro y hy
    by_contra hyK
    exact hy (hf0 (fun h => hyK (interior_subset h)))
  have hg : Continuous fun X => ENNReal.ofReal (f X) := ENNReal.continuous_ofReal.comp f.continuous
  refine ⟨f, f.continuous, hfc, fun X => (hfr X).1, ?_, ?_, ?_⟩
  · exact (closure_minimal hsupp hK.isClosed).trans hKU
  · intro h0
    have hpos : 0 < ν {X | ENNReal.ofReal (f X) ≠ 0} := by
      refine IsOpen.measure_pos ν (isOpen_ne_fun hg continuous_const) ⟨x, ?_⟩
      have : f x = 1 := hf1 (Set.mem_singleton x)
      simp [this]
    exact hpos.ne' (ae_iff.1 ((lintegral_eq_zero_iff hg.measurable).1 h0))
  · exact (f.continuous.integrable_of_hasCompactSupport hfc).lintegral_lt_top.ne

theorem exists_compactOpen {W : Type} [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W]
    [TotallyDisconnectedSpace W] [MeasurableSpace W] (ν : Measure W) [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {U : Set W} (hU : IsOpen U) {x : W} (hx : x ∈ U) :
    ∃ A : Set W, IsCompact A ∧ IsOpen A ∧ A ⊆ U ∧ ν A ≠ 0 ∧ ν A ≠ ⊤ := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨C, hC, hxC, hCK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (X := W)).exists_subset_of_mem_open hxK
    isOpen_interior
  have hCc : IsCompact C := hK.of_isClosed_subset hC.1 (hCK.trans interior_subset)
  exact ⟨C, hCc, hC.2, (hCK.trans interior_subset).trans hKU, (hC.2.measure_pos ν ⟨x, hxC⟩).ne',
    hCc.measure_lt_top.ne⟩

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem gramR_ratTup_apply (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → E) (a c : Fin n) :
    gramR R σ J (ratTup R Y) a c = inclR R (gramE σ J Y a c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramR, gramE, hR, hE, hform, ratTup, JR, sigR, inclR, map_sum, map_mul]

theorem exists_unit_vector (R : Type) [CommRing R] [Algebra F R] {J : Matrix (Fin 2) (Fin 2) E}
    (hA : Aniso σ J) : ∃ X : Fin 1 → Fin 2 → R ⊗[F] E, IsUnit (gramR R σ J X).det := by
  have hx : hE σ J (fun _ => 1) (fun _ => 1) ≠ 0 := fun h => one_ne_zero (congrFun (hA _ h) 0)
  refine ⟨ratTup R fun _ _ => 1, ?_⟩
  rw [Matrix.det_fin_one, gramR_ratTup_apply]
  exact (IsUnit.mk0 _ hx).map (inclR R)

end Alg

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isOpen_unit (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hloc : IsLocR R) (J : Matrix (Fin 2) (Fin 2) E) :
    IsOpen {X : Fin 1 → Fin 2 → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hu, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨-, -, -, -, -, -, -, -, -, t10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  have hO : IsOpen {r : R | IsUnit r} := hu.isOpen_range
  exact (PI.VolStabS.isOpen_isUnit_det R hO 1).preimage (t10 1 2 J)

theorem exists_test_fun (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hA : Aniso σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hl : lam.IsAddHaarMeasure) :
    ∃ φ : (Fin 1 → Fin 2 → R ⊗[F] E) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧
      tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det} ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 2) ≠ 0 ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 2) ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 2
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 2
  obtain ⟨X, hX⟩ := exists_unit_vector R hA
  exact exists_bump _ (isOpen_unit hcm R hloc J) hX

theorem exists_test_set (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hA : Aniso σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    [TotallyDisconnectedSpace R] (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hl : lam.IsAddHaarMeasure) :
    ∃ A : Set (Fin 1 → Fin 2 → R ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR R σ J X).det} ∧ coordW R b lam 1 2 A ≠ 0 ∧ coordW R b lam 1 2 A ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 2
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 2
  haveI : TotallyDisconnectedSpace (R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.totallyDisconnectedSpace
  obtain ⟨X, hX⟩ := exists_unit_vector R hA
  exact exists_compactOpen _ (isOpen_unit hcm R hloc J) hX

end Loc

theorem testEx : TestEx := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam _ _ _ _ S
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨φ, h1, h2, h3, h4, h5, h6⟩ := exists_test_fun hcm hA (Ainf F) hLi b li hli.1
  have hA' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} ∧ coordW (Fv F v) b (lam v) 1 2 A ≠ 0 ∧
      coordW (Fv F v) b (lam v) 1 2 A ≠ ⊤ := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact exists_test_set hcm hA (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) b (lam v) (hlam v).1
  choose A0 hc ho hs hn ht using hA'
  classical
  have hv : vol b li lam S φ (fun v => if v ∈ S then A0 v else latV b v) =
      (∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 2)) * ∏ v ∈ S, coordW (Fv F v) b (lam v) 1 2 (A0 v) := by
    unfold vol
    congr 1
    exact Finset.prod_congr rfl fun v hvS => by simp [hvS]
  refine ⟨φ, fun v => if v ∈ S then A0 v else latV b v, ⟨h1, h2, h3, h4, ?_, ?_⟩, ?_, ?_⟩
  · intro v hvS
    simp only [hvS, if_true]
    exact ⟨hc v, ho v, hs v⟩
  · intro v hvS
    simp [hvS]
  · rw [hv]
    exact mul_ne_zero h5 (Finset.prod_ne_zero_iff.2 fun v _ => hn v)
  · rw [hv]
    exact ENNReal.mul_ne_top h6 (ENNReal.prod_ne_top fun v _ => ht v)

end GlobalTheory.CompanionTheory.SW.MassTest
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedSumLimit
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem tsum_unitVec_eq {F : Type} [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (h : F → ℝ) :
    ∑' x : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}, h (x.1 ()) =
      ∑' x : F, (IntOut T).indicator h x := by
  let e : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} ≃ (IntOut T) :=
    (Equiv.funUnique Unit F).subtypeEquiv (fun x => by
      constructor
      · intro hx v hv
        exact hx v hv ()
      · intro hx v hv i
        exact hx v hv)
  rw [← tsum_subtype (IntOut T) h]
  exact e.tsum_eq (fun y : IntOut T => h y.1)

theorem tsum_eq_zero_add_of_finset {F : Type} [Field F] (h : F → ℝ) (B : Finset F) (hB : ∀ x ∈ B, x ≠ 0)
    (hh : ∀ x, x ≠ 0 → x ∉ B → h x = 0) :
    ∑' x : F, h x = h 0 + ∑' β : {β : F // β ≠ 0}, h β.1 := by
  rw [tsum_ne_zero_eq_sum h B hB hh, tsum_eq_sum (s := insert 0 B) ?_, Finset.sum_insert (fun h0 => hB 0 h0 rfl)]
  intro x hx
  simp only [Finset.mem_insert, not_or] at hx
  exact hh x hx.1 hx.2

theorem integral_unitVec_eq {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (f : X → ℝ) :
    ∫ y, f (y ()) ∂(Measure.pi fun _ : Unit => μ) = ∫ y, f y ∂μ :=
  (measurePreserving_funUnique μ Unit).integral_comp' (g := f)

theorem tendsto_truncSum : Equi → CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ),
    Continuous G → HasCompactSupport G → (∀ v ∈ T, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) →
    Tendsto (truncSum θ G T ψ) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ T, ∫ s, ψ v s ∂(lam v))) := by
  intro hE hC F _ _ hF θ hθ li lam hli hlam T G ψ hG hGc hψ
  have hlocI : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : LocallyCompactSpace (Ainf F) := hlocI.2.1
  have : SecondCountableTopology (Ainf F) := hlocI.2.2.1
  have := hli.1
  have : SigmaFinite li := inferInstance
  have hsf : ∀ v, SigmaFinite (lam v) := fun v => by
    have hloc : IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    have : LocallyCompactSpace (Fv F v) := hloc.2.1
    have : SecondCountableTopology (Fv F v) := hloc.2.2.1
    have := (hlam v).1
    infer_instance
  have key := hE F hF θ hθ li lam hli hlam Unit T (fun y => G (y ())) (fun v y => ψ v (y ()))
    (hG.comp (continuous_apply ())) (hGc.comp_homeomorph (Homeomorph.funUnique Unit (Ainf F)))
    (fun v hv => ⟨(hψ v hv).1.comp (continuous_apply ()),
      (hψ v hv).2.comp_homeomorph (Homeomorph.funUnique Unit (Fv F v))⟩)
  rw [integral_unitVec_eq li G,
    Finset.prod_congr rfl (fun v _ => haveI := hsf v; integral_unitVec_eq (lam v) (ψ v))] at key
  simp only [Fintype.card_unit, mul_one] at key
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hpow : Tendsto (fun ε : ℝ => ε ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0)) (𝓝 0)
        (𝓝 ((0 : ℝ) ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0))) :=
      ((continuous_pow _).mul continuous_const).tendsto 0
    rw [zero_pow hd.ne', zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hsub := key.sub hpow
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨B, hB, hh⟩ := truncTerm_finite hC F hF θ hθ T G ψ hGc (fun v hv => (hψ v hv).2) ε hε
  have h0mem : (0 : F) ∈ IntOut T := fun v _ => by
    rw [map_zero]
    exact zero_mem _
  have e := (tsum_unitVec_eq T (fun x => G (θ ε * algebraMap F (Ainf F) x) *
    ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x))).trans (tsum_eq_zero_add_of_finset _ B hB hh)
  rw [Set.indicator_of_mem h0mem] at e
  rw [e]
  simp only [truncSum, map_zero, mul_zero]
  ring

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeTSurjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem wedgeT_surjective (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] :
    Function.Surjective (wedgeT (R := R) V) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span (R := R) (n := 2) (M := V),
    Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  refine ⟨v 0 ⊗ₜ v 1, ?_⟩
  rw [wedgeT_tmul]
  congr 1
  funext i; fin_cases i <;> rfl

theorem wedgeOf_of_low : LowSt → WedgeOfSt := by
  intro hL R _ P _ _ F g hH hV hBC hV2 hspan
  have : Finite Pᵒᵖ := Finite.of_injective unop unop_injective
  have hV' := hV
  obtain ⟨hf, hp, -⟩ := hV'
  have hκ : Function.Surjective (TensorProduct.lift (cup F)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1 ⊗ₜ x.2, rfl⟩
  have hinj : Function.Injective (TensorProduct.map (iotaQ F) (iotaQ F)) := by
    have e : TensorProduct.map (iotaQ F) (iotaQ F) =
        ((iotaQ F).lTensor (QC F)) ∘ₗ ((iotaQ F).rTensor (H1 F)) := by
      rw [LinearMap.lTensor_comp_rTensor]
    rw [e, LinearMap.coe_comp]
    exact (GlobalTheory.T.first_cohomology_inclusion_tensor_injective R _ F hBC (QC F)).comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ (iotaQ_injective F))
  have hker : LinearMap.ker (TensorProduct.lift (cup F)) ≤ LinearMap.ker (wedgeT (R := R) (H1 F)) := by
    intro t ht
    have h1 := _root_.GlobalTheory.CompanionTheory.WedgeOf.hopf_cross_antisymm hL R _ F hH t ht
    have h2 := GlobalTheory.T.cross_product_kernel_quotient_vanishing R _ F _ h1
    have h3 := hinj (h2.trans (map_zero _).symm)
    exact GlobalTheory.T.wedge_of_symmetric_tensor_zero R _ t h3
  let s : H2 F →ₗ[R] ⋀[R]^2 (H1 F) :=
    (LinearMap.ker (TensorProduct.lift (cup F))).liftQ (wedgeT (R := R) (H1 F)) hker ∘ₗ
      (LinearMap.quotKerEquivOfSurjective _ hκ).symm.toLinearMap
  have hs : ∀ t, s (TensorProduct.lift (cup F) t) = wedgeT (R := R) (H1 F) t := by
    intro t
    have : (LinearMap.quotKerEquivOfSurjective _ hκ).symm (TensorProduct.lift (cup F) t) =
        Submodule.Quotient.mk t := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  have hsurj : Function.Surjective s := fun y ↦ by
    obtain ⟨t, rfl⟩ := wedgeT_surjective R (H1 F) y
    exact ⟨_, hs t⟩
  have hb := _root_.GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB R _ _ _ hV2 (_root_.GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two R _ g hV) s hsurj
  refine ⟨(LinearEquiv.ofBijective s hb).symm, fun a b ↦ ?_⟩
  rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  have := hs (a ⊗ₜ b)
  rw [wedgeT_tmul] at this
  exact this.symm

end GlobalTheory.CompanionTheory.WedgeOf
end
end

