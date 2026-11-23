module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import GroundTheory.AutomorphicForms.GeometricLemmaCells
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0321
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0325
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0310
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0311
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.Rodier

section Pi

variable {α : Type} [Fintype α] {Γ : α → Type} [∀ a, Group (Γ a)]

abbrev piSub (H : ∀ a, Subgroup (Γ a)) : Subgroup (∀ a, Γ a) := Subgroup.pi Set.univ H

def piChar {H : ∀ a, Subgroup (Γ a)} (χ : ∀ a, H a →* ℂˣ) : piSub H →* ℂˣ where
  toFun m := ∏ a, χ a ⟨m.1 a, m.2 a (Set.mem_univ a)⟩
  map_one' := Finset.prod_eq_one fun a _ => map_one (χ a)
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => map_mul (χ a) ⟨x.1 a, x.2 a (Set.mem_univ a)⟩ ⟨y.1 a, y.2 a (Set.mem_univ a)⟩

end Pi

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

abbrev pm (w : Equiv.Perm (Fin N)) : GL (Fin N) k := GroundTheory.Automorphic.permGL k w

def cell (w : Equiv.Perm (Fin N)) : Set (GL (Fin N) k) :=
  {g | ∃ p ∈ parab k (stdBlocks d hd), ∃ n ∈ unipB k (Fin N), g = p * pm k w * n}

def wKey (i : Fin N) : (Fin h)ᵒᵈ ×ₗ Fin N := toLex (OrderDual.toDual (blk (stdBlocks d hd) i), i)

def wOpen : Equiv.Perm (Fin N) := Tuple.sort (wKey d hd)

variable {k}
variable {W : Type} [AddCommGroup W] [Module ℂ W]

def openFns (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) : Submodule ℂ (IndSp (stdBlocks d hd) ρ) where
  carrier := {f | ∀ g, f.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)}
  add_mem' := by
    intro a b ha hb g hg
    by_cases h1 : a.1.1 g = 0
    · refine hb g fun h2 => hg ?_
      show a.1.1 g + b.1.1 g = 0
      rw [h1, h2, add_zero]
    · exact ha g h1
  zero_mem' := fun g hg => absurd rfl hg
  smul_mem' := by
    intro c a ha g hg
    refine ha g fun h1 => hg ?_
    show c • a.1.1 g = 0
    rw [h1, smul_zero]

variable (k)

abbrev unipM : Subgroup (Levi k fun a => Fin (d a)) := piSub fun a => unipB k (Fin (d a))

variable {k}

abbrev whitM (ψ : AddChar k Circle) : unipM k d →* ℂˣ := piChar fun a => whitChar ψ (d a)

variable (k)

def unipU : Subgroup (GL (Fin N) k) :=
  unipB k (Fin N) ⊓ (unipRadLower k (stdBlocks d hd)).comap (MulAut.conj (pm k (wOpen d hd))).toMonoidHom

def unipL : Subgroup (GL (Fin N) k) :=
  unipB k (Fin N) ⊓ (leviEmb k (stdBlocks d hd)).range.comap (MulAut.conj (pm k (wOpen d hd))).toMonoidHom

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem OpenFactor.mem_unipL {u : GL (Fin N) k} : u ∈ unipL k d hd ↔
    u ∈ unipB k (Fin N) ∧
      pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ (leviEmb k (stdBlocks d hd)).range := by
  simp only [unipL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]

end GlobalTheory.CompanionTheory.Rodier

namespace GlobalTheory.CompanionTheory.Rodier

def smInt {X W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W] (μ : MeasureTheory.Measure X) (φ : X → W) : W :=
  ∑ᶠ v : W, (((μ (φ ⁻¹' {v})).toReal : ℝ) : ℂ) • v

end GlobalTheory.CompanionTheory.Rodier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvariance
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil

theorem JR_sim {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (γ : GL (Fin M) E) (l : F)
    (hγ : cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J) :
    cT (sigR R σ) ((bc (inclR R) γ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        ((bc (inclR R) γ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (algebraMap R (R ⊗[F] E) (algebraMap F R l)) • JR R J := by
  rw [← GlobalTheory.CompanionTheory.SW.HIsom.JR_conj, hγ]
  ext i j
  change inclR R (algebraMap F E l * J i j) = algebraMap R (R ⊗[F] E) (algebraMap F R l) * inclR R (J i j)
  rw [map_mul]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l

theorem simil : PositivityTheory.Rg.Mass.Simil := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ _ hli hlam hμ h𝓕 hmi hm β β' hβ hβ' hs hs' c hc
  have hl0 : β' / β ≠ 0 := div_ne_zero hβ' hβ
  obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.CompanionTheory.SimilExists.exists_similitude F E σ hcm J hJ β β' hβ hβ' hs hs'
  obtain ⟨μ', 𝓕', hμ', h𝓕', hth⟩ := _root_.GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil F E σ hcm 2 J hJ μ 𝓕 hμ h𝓕 γ (β' / β) hl0 hγ
  have hT : (fun _ _ => algebraMap F E β' : Matrix (Fin 1) (Fin 1) E) =
      (algebraMap F E (β' / β)) • (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) := by
    funext a b'
    change algebraMap F E β' = algebraMap F E (β' / β) * algebraMap F E β
    rw [← map_mul, div_mul_cancel₀ _ hβ]
  have hth1 := hth 1 _ _ hT
  have hind := _root_.GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep F E σ hcm 2 J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕' 1 (fun _ _ => algebraMap F E β)
  change (thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β)).map _ = thetaMeas σ J μ 𝓕 (PositivityTheory.Rg.Mass.sph σ J β') at hth1
  change thetaMeas σ J μ 𝓕 (PositivityTheory.Rg.Mass.sph σ J β) = thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β) at hind
  obtain ⟨ai, a, hau, hai, hav⟩ := _root_.GlobalTheory.CompanionTheory.SW.PfAct.product_formula_actTup F E σ hcm 1 2 γ
  obtain ⟨ci, cv, hcu, hci, hcv⟩ := _root_.GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module F E σ hcm (β' / β) hl0
  obtain ⟨-, -, -, -, hq, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ai ci a cv hau hcu
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := SWIsom.haar_of_loc σ hcm (Ainf F) hLi b li hli.1 1 2
  have hWv := fun v => SWIsom.haar_of_loc σ hcm (Fv F v) (hLv v) b (lam v) (hlam v).1 1 2
  have hJR : ∀ (R : Type) [CommRing R] [Algebra F R],
      cT (sigR R σ) ((bc (inclR R) γ : GL (Fin 2) (R ⊗[F] E)) : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) * JR R J *
        ((bc (inclR R) γ : GL (Fin 2) (R ⊗[F] E)) : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) =
        (algebraMap R (R ⊗[F] E) (algebraMap F R (β' / β))) • JR R J := fun R _ _ => JR_sim R σ J γ _ hγ
  have hunit : ∀ (R : Type) [CommRing R] [Algebra F R] [Nontrivial R], IsUnit (algebraMap F R (β' / β)) :=
    fun R _ _ _ => (IsUnit.mk0 _ hl0).map _
  have sInf := _root_.GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude F E σ hcm 2 J hJ (Ainf F) hLi 1 _ _ mi hWi.1 hWi.2 hmi _ _ (hunit _) (hJR _) ai ci
    (hai _ hWi.1) (hci _ hWi.2)
  have sV := fun v => _root_.GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude F E σ hcm 2 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v) _ _ (hunit _)
    (hJR _) (a v) (cv v) (hav v _ (hWv v).1) (hcv v _ (hWv v).2)
  have hS : ∀ (R : Type) [CommRing R] [Algebra F R], scalH R σ (algebraMap F R (β' / β))
      (hermScal R σ (algebraMap F R β)) = hermScal R σ (algebraMap F R β') := fun R _ _ => by
    rw [scalH_hermScal, ← map_mul, div_mul_cancel₀ _ hβ]
  have hproj : ∀ X : Fin 1 → Fin 2 → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) γ) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) γ) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) γ) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) γ) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact SWIsom.map_actTup (fstA F) γ X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) γ) X) =
          actTup (Af F) (bc (inclR (Af F)) γ) (projFin X) := by
        funext a i
        exact SWIsom.map_actTup (sndA F) γ X a i
      rw [h1]
      funext a i
      exact SWIsom.map_actTup (evalV F v) γ (projFin X) a i
  have hfin : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β')) (latV b v) < ⊤ := by
    intro v
    haveI := (_root_.GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hcm 2 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermScal (Fv F v) σ (algebraMap F _ β'))).1
    exact ((_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm d b 1 2).2.2.2.1 v).1.measure_lt_top
  have key := euler_move_c F E σ hcm d b 1 2 (thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β)) (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β')))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β)))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    (actTup (AF F) (bc (inclR (AF F)) γ))
    (actTup (Ainf F) (bc (inclR (Ainf F)) γ)) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) γ))
    (SWIsom.measurable_actTup σ hcm (AF F) _) (SWIsom.measurable_of_loc σ hcm (Ainf F) hLi _)
    (fun v => SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hcm d b 1 2).2.1 γ) (ai / ci) (fun v => a v / cv v) hq
    (by rw [sInf, hS]) (fun v => by rw [sV v, hS]) hfin c
  unfold PositivityTheory.Rg.Mass.EP at hc ⊢
  rw [hind] at hc
  rw [← hth1]
  exact key hc

end GlobalTheory.CompanionTheory.SW.MassSimil

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFacts
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobOpsPf

open GlobalTheory.CompanionTheory.RCalc (Rd_congr Rd_add Rd_smul Rd_contDiffOn differentiableAt_of_smooth gel_contDiffOn Rd_gel gel_right
  gel_post fderiv_comp_clm fderiv_post mulR mapsTo_mulR)
open GlobalTheory.CompanionTheory.SobSecK (Rw_congr Rw_smooth Rw_append Rd_sum_cf)

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rw_add (w : List (Bool × Fin n × Fin n)) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) : Set.EqOn (Rw w (f + f')) (Rw w f + Rw w f') (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_add (bs p) (Rw_smooth w hf) (Rw_smooth w hf') hx)

theorem Rw_smul (w : List (Bool × Fin n × Fin n)) (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rw w (c • f)) (c • Rw w f) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_smul c (bs p) (Rw_smooth w hf) hx)

theorem Om_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Om f) (GLs n) :=
  ((gel_contDiffOn true 2 hf).add (gel_contDiffOn false 2 hf)).const_smul (2 : ℂ)

theorem Rd_Om (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Om f) g = Om (Rd X f) g := by
  have h1 := gel_contDiffOn true 2 hf
  have h2 := gel_contDiffOn false 2 hf
  have h3 : ContDiffOn ℝ ∞ (gel true 2 f + gel false 2 f) (GLs n) := h1.add h2
  have e1 := Rd_smul (2 : ℂ) X h3 hg
  have e2 := Rd_add X h1 h2 hg
  simp only [Pi.smul_apply, Pi.add_apply] at e1 e2
  simp only [Om, Pi.smul_apply, Pi.add_apply]
  rw [e1, e2, Rd_gel X true 2 hf hg, Rd_gel X false 2 hf hg]

theorem Rw_Om (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rw w (Om f)) (Om (Rw w f)) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_Om (bs p) (Rw_smooth w hf) hx)

theorem Rd_translate (X : Mat n) {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => f (y * x)) g = Rd (x⁻¹ * X * x) f (g * x) := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have hd := differentiableAt_of_smooth hf (mapsTo_mulR hx hg)
  have e : g * x * (x⁻¹ * X * x) = g * X * x := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have := fderiv_comp_clm (mulR x) hd (g * X)
  simp only [Rd, e]
  exact this

theorem Rd_post (X : Mat n) (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd X (fun y => A (f y)) g = A (Rd X f g) :=
  fderiv_post A (differentiableAt_of_smooth hf hg) _

theorem post_smooth (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => A (f y)) (GLs n) :=
  (A.restrictScalars ℝ).contDiff.comp_contDiffOn hf

theorem Rw_post (w : List (Bool × Fin n × Fin n)) (A : V →L[ℂ] V) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : Set.EqOn (Rw w (fun y => A (f y))) (fun y => A (Rw w f y)) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_post (bs p) A (Rw_smooth w hf) hx)

theorem Om_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Om (fun y => A (f y)) g = A (Om f g) := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_post A _ _ hf hg, map_smul, map_add (f := _)]

theorem Om_translate {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Om (fun y => f (y * x)) g = Om f (g * x) := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_right _ _ hx hf hg]

theorem translate_smooth {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => f (y * x)) (GLs n) :=
  hf.comp (mulR x).contDiff.contDiffOn (mapsTo_mulR hx)

end Words

section Sob

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem val_mem (y : G n) : y.val ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.ByParts.val_mem_GLs y

theorem sob_congr {f h : Mat n → V} (hf : Sob μ f) (e : Set.EqOn f h (GLs n)) : Sob μ h :=
  ⟨hf.1.congr fun _ hx => (e hx).symm, fun w =>
    MemLp.ae_eq (ae_of_all _ fun y => Rw_congr w e (val_mem y)) (hf.2 w)⟩

theorem sob_add {f h : Mat n → V} (hf : Sob μ f) (hh : Sob μ h) : Sob μ (f + h) :=
  ⟨hf.1.add hh.1, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_add w hf.1 hh.1 (val_mem y)).symm)
    ((hf.2 w).add (hh.2 w))⟩

theorem sob_smul (c : ℂ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (c • f) :=
  ⟨hf.1.const_smul c, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_smul w c hf.1 (val_mem y)).symm)
    ((hf.2 w).const_smul c)⟩

theorem sob_zero {f : Mat n → V} (hf : Sob μ f) : Sob μ (0 : Mat n → V) := by
  simpa using sob_smul (0 : ℂ) hf

theorem sob_sum {ι : Type} (s : Finset ι) {f₀ : Mat n → V} (h₀ : Sob μ f₀) {F : ι → Mat n → V}
    (hF : ∀ i, Sob μ (F i)) : Sob μ (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sob_zero h₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact sob_add (hF a) ih

theorem sob_Rw (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rw w f) :=
  ⟨Rw_smooth w hf.1, fun w' => by rw [Rw_append]; exact hf.2 _⟩

theorem sob_bs (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rd (bs p) f) :=
  sob_Rw [p] hf

theorem sob_Rd (X : Mat n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rd X f) := by
  refine sob_congr (f := ∑ p : Bool × Fin n × Fin n, ((GlobalTheory.CompanionTheory.SobSecK.cf X p : ℝ) : ℂ) • Rd (bs p) f)
    (sob_sum _ hf fun p => sob_smul _ (sob_bs p hf)) fun g _ => ?_
  rw [Rd_sum_cf X f g]
  simp only [Finset.sum_apply, Pi.smul_apply]

theorem sob_Eu (s : Bool) (a b : Fin n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Eu s a b f) :=
  sob_smul _ (sob_add (sob_Rd _ hf) (sob_smul _ (sob_Rd _ hf)))

theorem sob_Epow (s : Bool) (m : ℕ) {f : Mat n → V} (hf : Sob μ f) : ∀ a b, Sob μ (Epow s m a b f) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simpa [Epow, hab] using sob_zero hf
  | succ m ih =>
    intro a b
    exact sob_sum _ hf fun c => sob_Eu s a c (ih c b)

theorem sob_gel (s : Bool) (m : ℕ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (gel s m f) :=
  sob_sum _ hf fun a => sob_Epow s m hf a a

theorem sob_Om {f : Mat n → V} (hf : Sob μ f) : Sob μ (Om f) :=
  sob_smul _ (sob_add (sob_gel _ _ hf) (sob_gel _ _ hf))

theorem sob_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : Sob μ f) : Sob μ (fun y => A (f y)) :=
  ⟨post_smooth A hf.1, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_post w A hf.1 (val_mem y)).symm)
    (A.comp_memLp' (hf.2 w))⟩

variable [BorelSpace (G n)] [μ.IsHaarMeasure]

theorem memLp_translate (hU : Unimod) (h : G n) {F : Mat n → V} (hF : MemLp (fun y : G n => F y.val) 2 μ) :
    MemLp (fun y : G n => F (y.val * h.val)) 2 μ := by
  haveI := (hU n μ).1
  exact hF.comp_measurePreserving (measurePreserving_mul_right μ h)

theorem translate_memLp (hU : Unimod) (h : G n) (w : List (Bool × Fin n × Fin n)) :
    ∀ F : Mat n → V, Sob μ F → MemLp (fun y : G n => Rw w (fun z => F (z * h.val)) y.val) 2 μ := by
  induction w using List.reverseRecOn with
  | nil => exact fun F hF => memLp_translate hU h (hF.2 [])
  | append_singleton w p ih =>
    intro F hF
    rw [← Rw_append [p] w]
    have e : Set.EqOn (Rw [p] fun z => F (z * h.val)) (fun z => Rd (h.val⁻¹ * bs p * h.val) F (z * h.val)) (GLs n) :=
      fun g hg => Rd_translate (bs p) (val_mem h) hF.1 hg
    exact MemLp.ae_eq (ae_of_all _ fun y => (Rw_congr w e (val_mem y)).symm) (ih _ (sob_Rd _ hF))

theorem sob_translate (hU : Unimod) (h : G n) {F : Mat n → V} (hF : Sob μ F) : Sob μ (fun y => F (y * h.val)) :=
  ⟨translate_smooth (val_mem h) hF.1, fun w => translate_memLp hU h w F hF⟩

end Sob

theorem sobOps : SobOps := by
  intro n _ _ μ _ V _ _ _ hU _ f hf
  refine ⟨sob_Om hf, fun w => sob_Rw w hf, fun w g hg => Rw_Om w hf.1 hg, fun a f' hf' => ⟨sob_add (sob_smul a hf) hf', ?_⟩,
    fun h A => ⟨sob_post A (sob_translate hU h hf), fun g hg => ?_⟩⟩
  · intro g hg
    have hs : ContDiffOn ℝ ∞ (a • f) (GLs n) := hf.1.const_smul a
    have e1 := GlobalTheory.CompanionTheory.WaveK.Lin.Om_add hs hf'.1 hg
    have e2 := GlobalTheory.CompanionTheory.WaveK.Lin.Om_smul a hf.1 hg
    simp only [Pi.add_apply, Pi.smul_apply] at e1 e2
    rw [e1, e2]
  · rw [Om_post A (translate_smooth (val_mem h) hf.1) hg, Om_translate (val_mem h) hf.1 hg]

end GlobalTheory.CompanionTheory.SobOpsPf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsUniformGenerators
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem exists_alg_of_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ (n₁ : ℤ) (W : ∀ n : ℤ, Set Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ n e, W n ⊆ twSecs H n (S e)) → (∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W n, x - b ∈ twPow I H n P (e + 1)) → ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  intro A _ _ I X _ _ H hA P hP S hS n₁ W hW hgen
  have hH := hA.isLB
  let F : Set (Subobject P) := {B | (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ≤ S e}
  have h0 : (0 : Γ(GlobalTheory.twistZ P H n₁, ⊤)) ∈ twSecs H n₁ (S 0) := ⟨0, map_zero _⟩
  obtain ⟨b₀, hb₀, -⟩ := hgen n₁ le_rfl 0 0 h0
  have hF : F.Nonempty :=
    ⟨genSub hH n₁ b₀, _root_.GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub hH hP.1 n₁ b₀, fun e => _root_.GlobalTheory.CompanionTheory.GE.TwGen.genSub_le hH (S e) n₁ b₀ (hW n₁ e hb₀)⟩
  obtain ⟨M, ⟨hMq, hMS⟩, hMmax⟩ := GlobalTheory.T.coherent_noetherian_maximal_subsheaf hP F hF (fun B hB => hB.1)
  have hgenM : ∀ n, ∀ b ∈ W n, genSub hH n b ≤ M := by
    intro n b hb
    have hmem : M ⊔ genSub hH n b ∈ F :=
      ⟨(GlobalTheory.T.quasicoherent_sup_sections hP.1 M (genSub hH n b) hMq (_root_.GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub hH hP.1 n b)).1,
        fun e => sup_le (hMS e) (_root_.GlobalTheory.CompanionTheory.GE.TwGen.genSub_le hH (S e) n b (hW n e hb))⟩
    rw [← hMmax _ hmem le_sup_left]
    exact le_sup_right
  refine ⟨M, hMq, fun e => le_antisymm (sup_le (hMS e) (hS.pow_le e)) ?_⟩
  have hSe : IsCoherent (S e : X.Modules) := GlobalTheory.T.coherent_subobject_coherent hP (S e) (hS.qcoh e)
  obtain ⟨n₀, hn₀⟩ := _root_.GlobalTheory.CompanionTheory.GE.TwGen.le_of_genSub_le hA (S e) hSe
  refine hn₀ (max n₀ n₁) (le_max_left _ _) _ fun x hx => ?_
  obtain ⟨b, hb, hxb⟩ := hgen (max n₀ n₁) (le_max_right _ _) e x hx
  rw [← add_sub_cancel b x]
  exact (_root_.GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le hH _ b (x - b)).trans (sup_le_sup (hgenM _ b hb) (_root_.GlobalTheory.CompanionTheory.GE.TwGen.genSub_le_powSub I hH hP.1 _ _ _ hxb))

end GlobalTheory.CompanionTheory.GE.TwGen
end

