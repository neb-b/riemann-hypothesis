module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0849
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0847
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0848

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MtLatFgOfReps
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie

theorem fg_of_eval {R G W I : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup W] [Module R W] [Finite I]
    (L : Submodule R (G → W)) (y : I → G) (C : I → Submodule R W) (hC : ∀ c, (C c).FG)
    (hmem : ∀ f ∈ L, ∀ c, f (y c) ∈ C c) (hinj : ∀ f ∈ L, (∀ c, f (y c) = 0) → f = 0) : L.FG := by
  haveI : ∀ c, IsNoetherian R (C c) := fun c => isNoetherian_of_fg_of_noetherian _ (hC c)
  let ev : L →ₗ[R] ∀ c, C c :=
    { toFun := fun f c => ⟨f.1 (y c), hmem f.1 f.2 c⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun f hf => ?_
    exact Subtype.ext (hinj f.1 f.2 fun c => congrArg Subtype.val (congrFun hf c))
  haveI : IsNoetherian R L := isNoetherian_of_injective ev hev
  exact Module.Finite.iff_fg.1 inferInstance

section Eval

variable {D : D7} {S T : HSp D} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
  {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ}

theorem eq_zero_of_reps (B : Base S T) (t : Twist D Circle) {I : Type} {y : I → Bridge.Gf S}
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) {f : Bridge.Gf S → PolF D T.rank S.rank} (hf : f ∈ B.formsC t)
    (h0 : ∀ c, f (y c) = 0) : f = 0 := by
  have hlaw : B.HasLaw t f := ((B.mem_formsC).1 hf).2
  funext h
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := hy h
  have h1 := hlaw γ (y c) k
  rw [h0 c, map_zero, smul_zero, ← e] at h1
  exact h1

theorem mtLat_fg_of_reps [IsNoetherianRing O] (B : Base S T) (t : Twist D Circle) {I : Type} [Finite I] {y : I → Bridge.Gf S}
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) (hfg : ∀ c, (B.coefLat σ emb O (y c)).FG) :
    (B.mtLat σ emb O t).FG :=
  fg_of_eval _ y (fun c => B.coefLat σ emb O (y c)) hfg (fun _ hf c => ((B.mem_mtLat σ emb O).1 hf).2 (y c))
    fun _ hf h0 => eq_zero_of_reps B t hy ((B.mem_mtLat σ emb O).1 hf).1 h0

end Eval

theorem latFG_of_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ρ.LatFG := by
  intro D N X ρ hρ i j b k Q ψ hT
  obtain ⟨hg, ha, -⟩ := _root_.GlobalTheory.TwistGood.tw_good D N X ρ hρ i j b k Q ψ hT
  have hc := hρ.classes i j b _ hg ha
  haveI : IsNoetherianRing (ρ.eOk i b k).range :=
    isNoetherianRing_of_surjective (X.Ok i k) _ (ρ.eOk i b k).rangeRestrict (ρ.eOk i b k).rangeRestrict_surjective
  have hB := hρ.base i j b
  refine mtLat_fg_of_reps _ _ hc.reps fun c => ?_
  refine (GlobalTheory.T.fockHarmonicLattice_fg_and_spans_value_space D _ _ _ _ _ _ _ _ _ hB.wt (fun τ => ?_) (hρ.isCoefRing_k i b k) ?_).1
  · have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  · classical
    have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
        IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
      intro V Λ hΛ
      haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
      refine ⟨?_⟩
      obtain ⟨s, hs⟩ := hΛ.1.fg
      apply eq_top_iff.mpr
      intro y _
      let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
        ∑ i, ∑ j, star (x i) * V.gram i j * y j
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
      have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
        exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
      let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
        carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
        zero_mem' := by refine ⟨0, ?_⟩; simp [f]
        add_mem' := by
          rintro x z ⟨b, hb⟩ ⟨c, hc⟩
          refine ⟨b + c, ?_⟩
          change (b : D.host.E) + c = _
          rw [hb, hc]
          simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
        smul_mem' := by
          rintro c x ⟨b, hb⟩
          refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
          simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          change star (c : D.host.E) * _ = _
          ring }
      have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
        intro x hx
        obtain ⟨b, hb⟩ := ha x hx
        exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
      have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
        apply (hΛ.2 _).2
        intro x hx
        have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
        obtain ⟨b, hb⟩ := hxP
        refine ⟨b, ?_⟩
        rw [hb]
        dsimp only [f, Pi.smul_apply]
        simp only [smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
        Submodule.subset_span hy
      have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
        (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
      change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
        ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
      rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
      exact this
    haveI : Submodule.IsFullLattice D.host.E (ρ.B i j b).F.ΛS := hfull _ _ hB.frame.sdS
    haveI : Submodule.IsFullLattice D.host.E
        ((ρ.B i j b).latAt (finPt (Vc D j) (ρ.rep i j b (ρ.tw i b k Q ψ) c))) :=
      Formalism.UG.P.csGlob_lattice (F := D.host.F) (ρ.B i j b).F.ΛS (Module.Finite.iff_fg.2 hB.frame.sdS.1.fg)
        (Submodule.IsFullLattice.span_eq_top (A := D.host.E) (M := (ρ.B i j b).F.ΛS)) _
    infer_instance

end GlobalTheory.SeriesTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW
open scoped ComplexConjugate

namespace GlobalTheory.RSnmUnf

def padNat {m n : ℕ} (l : Fin m → ℕ) : Fin n → ℕ := fun i => if h : (i : ℕ) < m then l ⟨i, h⟩ else 0

theorem padNat_zero {m n : ℕ} : padNat (m := m) (n := n) 0 = 0 := by
  funext i; simp only [padNat, Pi.zero_apply]; split_ifs <;> rfl


open Classical in
def rsTermNM (q : ℕ) {n m : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) (v : Fin m → ℤ) : ℂ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    schurAt (padNat fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)
  else 0

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def uIntNM {m n : ℕ} (hmn : m + 1 ≤ n) (F : (Fin (m + 1) → Ad E) → ℂ) (φ : GA E n → ℂ) (φ' : GA E (m + 1) → ℂ)
    (x : ℝ) (h : GA E (m + 1)) : ℂ :=
  whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL hmn h) * conj (whit φ' h) * GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h) *
    ((GlobalTheory.RSnm.detAbs h : ℝ) : ℂ) ^ ((x : ℂ) - ((n : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2)

end GlobalTheory.RSnmUnf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionEmptySecondIsSubquotientFirst
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}

def falseEquiv (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0) : Fin (c false) ≃ Fin r :=
  Equiv.ofBijective (fun i => f ⟨false, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact ⟨i, rfl⟩
    | true => exact absurd i.2 (by omega)⟩

theorem mem_parab_all {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (g : GL (Fin r) R) : g ∈ parab R f := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  cases a with
  | false => exact absurd hab (by cases b <;> decide)
  | true => exact absurd i.2 (by omega)

theorem eq_one_true {R : Type} [CommRing R] (hc : c true = 0) (h : GL (Fin (c true)) R) : h = 1 :=
  Units.ext (Matrix.ext fun i _ => (Fin.cast hc i).elim0)

def levi {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0) :
    GL (Fin r) R →* Levi R (fun j => Fin (c j)) :=
  (leviProj R f).comp ((MonoidHom.id _).codRestrict (parab R f) (mem_parab_all f hc))

theorem levi_false {R : Type} [CommRing R] (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (g : GL (Fin r) R) : levi f hc g false = reix R (falseEquiv f hc).symm g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem deltaHalf_eq_one (hc : c true = 0) (g : Levi F (fun j => Fin (c j))) :
    deltaHalf F (fun j => Fin (c j)) g = 1 := by
  rw [deltaHalf_apply, Fintype.prod_bool]
  have h1 : modExp (fun j => Fin (c j)) false = 0 := by
    simp only [modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g true) = 1 := by
    rw [eq_one_true hc (g true), map_one]
  rw [h1, h2]
  simp

end GlobalTheory.EmptySecondBlockProd

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evOne (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) :
    (parInd f ρ).IntertwiningMap (ρ.comp (levi f hc)) where
  toLinearMap :=
    { toFun := fun x => x.1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    show x.1.1 (1 * g) = ρ (levi f hc g) (x.1.1 1)
    have := parInd_law f ρ x ⟨g, mem_parab_all f hc g⟩ 1
    rw [mul_one] at this
    rw [one_mul, this, deltaHalf_eq_one hc, Units.val_one, one_smul]
    rfl

theorem evOne_apply (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) (x : IndSp f ρ) :
    evOne f hc ρ x = x.1.1 1 := rfl

theorem evOne_injective (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (ρ : Representation ℂ (Levi F (fun j => Fin (c j))) W) : Function.Injective (evOne f hc ρ) := by
  refine (injective_iff_map_eq_zero (evOne f hc ρ)).2 fun x hx => ?_
  rw [evOne_apply] at hx
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have := parInd_law f ρ x ⟨g, mem_parab_all f hc g⟩ 1
  rw [mul_one] at this
  show x.1.1 g = 0
  rw [this, hx, map_zero, smul_zero]

end GlobalTheory.EmptySecondBlockProd

namespace GlobalTheory.EmptySecondBlockProd

variable {c : Bool → ℕ} {r : ℕ}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_smul_eq (hc : c true = 0) (σ : IrrRep (GL (Fin (c true)) F)) {z : σ.V} (hz : z ≠ 0)
    (y : σ.V) : ∃ a : ℂ, a • z = y := by
  let S : Subrepresentation σ.ρ := ⟨ℂ ∙ z, fun g v hv => by
    rw [eq_one_true hc g, map_one]
    exact hv⟩
  haveI := σ.irr
  rcases eq_bot_or_eq_top S with h | h
  · exfalso
    have : z ∈ S.toSubmodule := Submodule.mem_span_singleton_self z
    rw [h] at this
    exact hz this
  · have : y ∈ S.toSubmodule := by rw [h]; trivial
    exact Submodule.mem_span_singleton.1 this

def tensorMap (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)) (x₀ : ∀ j, (s j).V) :
    Representation.IntertwiningMap
      ((s false).ρ.comp (reix F (falseEquiv f hc).symm) : Representation ℂ (GL (Fin r) F) (s false).V)
      ((piTensor fun j => (s j).ρ).comp (levi f hc)) where
  toLinearMap := (PiTensorProduct.tprod ℂ).toLinearMap x₀ false
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      MultilinearMap.toLinearMap_apply, piTensor_tprod]
    congr 1
    funext j
    cases j with
    | false => simp [levi_false]
    | true => simp [eq_one_true hc (levi f hc g true)]

theorem tensorMap_surjective (f : (Σ j, Fin (c j)) ≃ Fin r) (hc : c true = 0)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)) (x₀ : ∀ j, (s j).V) (hx : x₀ true ≠ 0) :
    Function.Surjective (tensorMap f hc s x₀) := by
  show Function.Surjective (tensorMap f hc s x₀).toLinearMap
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, ha⟩ := exists_smul_eq hc (s true) hx (y true)
  refine ⟨a • y false, ?_⟩
  have e1 : y = Function.update (Function.update x₀ false (y false)) true (a • x₀ true) := by
    funext j
    cases j <;> simp [ha]
  show (PiTensorProduct.tprod ℂ).toLinearMap x₀ false (a • y false) = PiTensorProduct.tprod ℂ y
  rw [map_smul, MultilinearMap.toLinearMap_apply]
  conv_rhs => rw [e1, MultilinearMap.map_update_smul]
  congr 2
  funext j
  cases j <;> simp

theorem isSubquotient_multiProd : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r)
    (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → ∃ φ : Fin r ≃ Fin (c false),
      IsSubquotient (multiProd f fun j => (s j).ρ)
        ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) := by
  intro F _ _ _ _ r c f s hc
  haveI := nontrivial_of_irreducible (s true).irr
  obtain ⟨z, hz⟩ := exists_ne (0 : (s true).V)
  let x₀ : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) 0 z j
  refine ⟨(falseEquiv f hc).symm, ?_⟩
  exact (IsSubquotient.of_injective (evOne f hc _) (evOne_injective f hc _)).trans
    (IsSubquotient.of_surjective (tensorMap f hc s x₀) (tensorMap_surjective f hc s x₀ hz))

end GlobalTheory.EmptySecondBlockProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittakerStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
open GlobalTheory.MirTower GlobalTheory.CuspGeneric GlobalTheory.RSJ GlobalTheory.ZUnf in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
  ∃ c : ℝ, 0 < c ∧ ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω →
    π'.HasCentChar ω' → ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (𝓕 𝓕₀ : Set (GA E (m + 1))), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ →
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, 1 < x → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.ZEul.uInt φ φ' Φ N x) 𝓕₀ μ ∧
        GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = (c : ℂ) * ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ := by
  intro E _ _ _ m μ _
  refine ⟨1, one_pos, ?_⟩
  intro π π' ω ω' hω hω' hπ hπ' φ φ' hφ hφ' N Φ _hN hΦs _hΦc hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x _hx h1 h2
  have := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
  have := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
  have := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
  obtain ⟨𝓕P, h𝓕P⟩ : ∃ 𝓕P, IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ := by
    have : DiscreteTopology (ratMirU E (m + 1) m) := discrete_of_le_range (Subgroup.map_le_range _ _)
    exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ
  have h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ := NE_eq_ratMirU_zero (E := E) (m := m) ▸ h𝓕₀
  obtain ⟨hc, hl, hv⟩ := _root_.GlobalTheory.JSW.mspanR_cont_left_avg E m π ω hω hπ φ hφ
  obtain ⟨hc', hl', hv'⟩ := _root_.GlobalTheory.JSW.mspanR_cont_left_avg E m π' ω' hω' hπ' φ' hφ'
  have hΦcont : Continuous Φ := hΦs.continuous
  have hG := _root_.GlobalTheory.ZUnf.good_fT E m φ hc hl hv Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  have hG' := _root_.GlobalTheory.ZUnf.good_fT E m φ' hc' hl' hv' Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  obtain ⟨hwm, hwΓ, hwU⟩ := GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant E m N x
  have hU := GlobalTheory.MirTower.unfold_mirabolic E (m + 1) μ (GlobalTheory.StdCharConductor.psi E) (GlobalTheory.StdCharConductor.stdPsi_psi E)
    𝓕P 𝓕₀ h𝓕P h𝓕₀' (wt N x) hwm hwΓ hwU
  have hW : ∀ f : GA E (m + 1) → ℂ, Good (GlobalTheory.StdCharConductor.psi E) m f → ∀ g,
      GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := fun f hf g =>
    _root_.GlobalTheory.WhitCols.whit_eq_colWhit E m f hf.cont (fun γ hγ g => hf.left γ (isMir_of_mem_mirU_zero hγ) g) g
  have hd : ∫⁻ g in 𝓕P, ‖fT φ Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG]
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG]
    simp only [e]
    exact h1
  have hd' : ∫⁻ g in 𝓕P, ‖fT φ' Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG']
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG']
    simp only [e]
    exact h2
  obtain ⟨hI1, hI2, hEq⟩ := hU.2 _ _ hG hG' hd hd'
  have e1 : GlobalTheory.ZEul.uInt φ φ' Φ N x = fun g => GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g *
      conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g) * ((wt N x g : ℝ) : ℂ) := by
    funext g
    rw [uInt_eq hΦp, hW _ hG, hW _ hG']
  have e2 : (fun g => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)) =
      fun g => fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ) := funext fun g => psi_lastRow_eq hΦp φ φ' N x g
  have hfin : ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ := by
    rw [show (fun g => ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ) =
      fun g => ‖fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ)‖ₑ from funext fun g => by rw [psi_lastRow_eq hΦp]]
    exact hI1.2.ne
  refine ⟨by rw [e1]; exact hI2, ?_⟩
  have hUnfold := GlobalTheory.ZUnfTheta.zint_eq_mirabolic E m μ 𝓕 𝓕P h𝓕 h𝓕P
    φ φ' hc.measurable hc'.measurable hl hl' N Φ hΦcont x hfin
  rw [hUnfold, e2, Complex.ofReal_one, one_mul, e1]
  exact hEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalLocalFactorNormSq
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.RSCell

theorem wtS_eq_sum (N : ℕ) (a : Fin N → ℤ) :
    GlobalTheory.CellDec.wtS N a = ∑ i : Fin N, ((N : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * a i := by
  first
  | exact @_root_.GlobalTheory.WeightSumSplit.wtS_eq
  | exact _root_.GlobalTheory.WeightSumSplit.wtS_eq
  | (apply _root_.GlobalTheory.WeightSumSplit.wtS_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSumSplit.wtS_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSumSplit.wtS_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSumSplit.wtS_eq ..)

theorem locFac_eq_wtS_sphZ : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α : Fin (n + 1) → ℂ) (x : ℝ) (ν : Fin (n + 1) → ℤ), 0 ≤ ν (Fin.last n) →
    ENNReal.ofReal ((q : ℝ) ^ GlobalTheory.CellDec.wtS (n + 1) ν) * ENNReal.ofReal ((q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) *
      ‖GlobalTheory.RSCell.sphZ q α ν‖ₑ ^ 2 = GlobalTheory.RSCell.locFac q α x ν := by
  intro q hq n α x ν hlast
  by_cases hA : Antitone ν
  · have hnn : ∀ i, 0 ≤ ν i := fun i => le_trans hlast (hA (Fin.le_last i))
    have hAn : Antitone (fun i => (ν i).toNat) := fun i j h => Int.toNat_le_toNat (hA h)
    rw [GlobalTheory.RSCell.locFac, if_pos ⟨hA, hnn⟩, GlobalTheory.RSCell.sphZ, if_pos hA, GlobalTheory.JSW.sphW, if_pos hAn]
    set s := GlobalTheory.JSW.schurAt (fun i => (ν i).toNat) α
    set w : ℤ := GlobalTheory.CellDec.wtS (n + 1) ν with hw
    have hc : (∑ i : Fin (n + 1), ((((n + 1 : ℕ)) : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) * (((ν i).toNat : ℕ) : ℂ)) = ((w : ℤ) : ℂ) := by
      rw [hw, wtS_eq_sum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (((ν i).toNat : ℕ) : ℂ) = ((ν i : ℤ) : ℂ) by exact_mod_cast Int.toNat_of_nonneg (hnn i)]
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hsum : (((∑ i, (ν i).toNat : ℕ)) : ℝ) = ∑ i, (ν i : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      exact_mod_cast Int.toNat_of_nonneg (hnn i)
    rw [hc, hsum]
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (zpow_nonneg hq'.le _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq]
    have hre : (-((w : ℂ)) / 2).re = -(w : ℝ) / 2 := by simp
    rw [hre, mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ (-(w : ℝ) / 2)), ← Real.rpow_mul hq'.le,
      ← Real.rpow_intCast]
    have h1 : (q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ)) = 1 := by
      rw [← Real.rpow_add hq']
      norm_num
    calc (q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x)) *
          ((q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ)) * ‖s‖ ^ 2)
        = ((q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ))) * (‖s‖ ^ 2 * (q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) := by ring
      _ = _ := by rw [h1, one_mul]
  · rw [GlobalTheory.RSCell.locFac, if_neg (fun h => hA h.1), GlobalTheory.RSCell.sphZ, if_neg hA]
    simp

end GlobalTheory.RSCell
end

