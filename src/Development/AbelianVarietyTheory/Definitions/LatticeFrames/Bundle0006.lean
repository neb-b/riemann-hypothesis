module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.Model
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

section Gen
variable (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

theorem mt_mul (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one : mt V (1 : GA D V) = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem finM_mul (g h : GA D V) : finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  simp only [finM, mt_mul, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_mul

theorem finM_one : finM V hn (1 : GA D V) = 1 := by
  subst hn
  simp only [finM, mt_one, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem infM_eq (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn g τ = ((mt V g).map ((θ τ).comp (infPart D))).reindex (finCongr hn) (finCongr hn) := rfl

theorem infM_mul (g h : GA D V) (τ : D.what₂.Tau) : infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn
  simp only [infM_eq, mt_mul, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_mul

theorem infM_one (τ : D.what₂.Tau) : infM θ V hn (1 : GA D V) τ = 1 := by
  subst hn
  simp only [infM_eq, mt_one, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem infM_unit (g : GA D V) (τ : D.what₂.Tau) : IsUnit (infM θ V hn g τ).det := by
  have h := infM_mul θ V hn g g⁻¹ τ
  rw [mul_inv_cancel, infM_one] at h
  exact Matrix.isUnit_det_of_right_inverse h.symm

def finGL (g : GA D V) : GL (Fin n) (EF D) :=
  ⟨finM V hn g, finM V hn g⁻¹, by rw [← finM_mul, mul_inv_cancel, finM_one], by rw [← finM_mul, inv_mul_cancel, finM_one]⟩

theorem toEAf_conj (a : AE D) :
    toEAf D (cA D a) = Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem finGL_mem (g : GA D V) :
    finGL V hn g ∈ UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  subst hn
  have hg : cT (cA D) (mt V g) * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2
  have h2 := congrArg (fun M => M.map (toEAf D)) hg
  simp only [Matrix.map_mul] at h2
  change cT _ (finM V rfl g) * _ * finM V rfl g = _
  simp only [finM, finCongr_refl, Matrix.reindex_refl_refl]
  have e1 : cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((mt V g).map (toEAf D)) =
      (cT (cA D) (mt V g)).map (toEAf D) := by
    ext i j; simp only [cT, Matrix.transpose_apply, Matrix.map_apply, toEAf_conj]
  have e2 : V.gram.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) = (V.gram.map (incA D)).map (toEAf D) := rfl
  rw [e1, e2]; exact h2

def trFr {G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (g : GA D V) (y : Frames G) : Frames G :=
  ⟨fun τ => infM θ V hn g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (infM_unit θ V hn g τ).mul (y.2 τ)⟩

variable {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (yc : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))

theorem exists_dec (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S))) (g : GA D V) :
    ∃ p, IsDec S yc (finM V hn g) p := by
  obtain ⟨c, hc⟩ := hy (Quotient.mk'' ⟨finGL V hn g, finGL_mem V hn g⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := (@DoubleCoset.eq _ _ _ _ (yc c) _).1 hc
  obtain ⟨γ, hγ, e⟩ := Subgroup.mem_subgroupOf.1 ha
  refine ⟨(c, γ, ⟨b.1, Subgroup.mem_subgroupOf.1 hb⟩), hγ, ?_⟩
  have := congrArg (fun x => x.1.1) hab
  simp only at this
  rw [e]; exact this



end Gen

variable {u : D.what₂.Word}

variable {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)

end GlobalTheory.AdForm.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TermSumBoundOfPairsAmplitude
section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
namespace GlobalTheory.Core.Deg

def TypeU : Prop :=
  ∀ Cg cb Cw cT CT : ℝ, 0 < cb → 0 < cT → ∃ CH Ch Cp : ℝ, 0 ≤ CH ∧ 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∀ Cs : ℝ, Cp + 4 ≤ Cs →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → TypeAt large₂ Y u CH Cs C Ch Cp

def PairsDegOfType : Prop :=
  ∀ CH Ch Cp C : ℝ, 0 ≤ CH → 0 ≤ Ch → 0 ≤ Cp → 2 * (CH + 1) ≤ C → ∃ Cl₀ : ℝ,
    ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Cl₀ ≤ Cl →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → TypeAt large₂ Y u CH (Cp + 4) C Ch Cp →
      Formalism.L2.SG.RowsOther.PairsDegAmp (Y.tO u u) (PgC Y) (duC X Y u) D.R.k D.R.f

def TermSumBoundOfPairsAmplitude : Prop :=
  ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
    Formalism.L2.SG.RowsOther.PairsDegAmp (Y.tO u u) (PgC Y) (duC X Y u) D.R.k D.R.f → VanishingGramTermsBound Y u

end GlobalTheory.Core.Deg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.Top.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word}

theorem unit_transfer {A B m n : Type} [CommRing A] [CommRing B] [Fintype m] [Fintype n] (e : m ≃ n) (s : A →+* B) (σ : A →+* A)
    (τ : B →+* B) (hs : ∀ x, s (σ x) = τ (s x)) (J : Matrix n n A) (J' : Matrix m m B) (hJ : ∀ a b, J' a b = s (J (e a) (e b)))
    (y : Matrix n n A) (g : Matrix m m B) (hg : ∀ a b, g a b = s (y (e a) (e b))) (hy : Formalism.UG.cT σ y * J * y = J) :
    Formalism.UG.cT τ g * J' * g = J' := by
  ext i j
  have := congrArg s (congrFun (congrFun hy (e i)) (e j))
  rw [hJ, ← this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hg, hJ, hs]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← e.sum_comp]

theorem swap_inj : Function.Injective (Lev.swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective

theorem hasMat_pt {h h' : GA D D.sp.X'} {y} (h1 : HasMat h y) (h2 : HasMat h' y) : h = h' := by
  refine GlobalTheory.UnitarySplit.ga_ext _ ?_ ?_
  · have a : infHom D.sp.X' h = 1 := h1.1
    have b : infHom D.sp.X' h' = 1 := h2.1
    rw [a, b]
  · apply Units.ext
    ext i j
    apply swap_inj
    exact (h1.2 i j).trans (h2.2 i j).symm


set_option maxHeartbeats 1000000 in
theorem hasMat_exists (y : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ h : GA D D.sp.X', HasMat h y.1 := by
  let e := finCongr (rankP D)
  let s := (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm
  let r := (Matrix.reindexAlgEquiv D.host.F (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) e.symm)
  let g := Formalism.UG.bc s.toRingEquiv.toRingHom (Units.map r.toRingEquiv.toRingHom.toMonoidHom y.1)
  have hg : ∀ i j, g.1 i j = s (y.1.1 (e i) (e j)) := fun i j => rfl
  have hm : g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram := by
    have hs : ∀ x, s (Formalism.UG.sigR (sigD D) _ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig (s x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    have hy : Formalism.UG.cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) y.1.1 *
        (gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * y.1.1 =
        (gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := y.2
    have hJ : ∀ a b, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.X'.gram a b =
        s.toRingEquiv.toRingHom (((gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) (e a) (e b)) :=
      fun a b => rfl
    have key := unit_transfer e s.toRingEquiv.toRingHom (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) hs _ _ hJ y.1.1 g.1 hg hy
    exact key
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue D.sp.X' 1 g (one_mem _) hm
  refine ⟨k, k1, fun i j => ?_⟩
  rw [k2]
  exact s.symm_apply_apply _


theorem valC_ne_bot {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) : ValC G lam ≠ ⊥ := by
  intro h
  have hm : fnOf G (shiftOf lam) 1 (ten fun τ => extremal ℂ n (lam τ)) ∈ ValC G lam :=
    ⟨_, Submodule.subset_span ⟨_, fun τ => Submodule.subset_span ⟨[], rfl⟩, rfl⟩, rfl⟩
  rw [h, Submodule.mem_bot] at hm
  have := congrFun hm ⟨fun _ => 1, fun _ => by simp⟩
  simp [fnOf, ten, extremal, Formalism.GradedWeylDivisibility.hw, Formalism.GradedWeylDivisibility.lpMinor, MvPolynomial.eval_rename, RingHom.map_det] at this
  have e : ∀ (x : ι) (s : ℕ) (h1 h2 : s ≤ n), ((Matrix.of fun p q : Fin s => (MvPolynomial.X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) ℂ)).map
      ⇑(MvPolynomial.eval ((fun x : ι × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) ∘ Prod.mk x))) = 1 := by
    intro x s h1 h2
    ext p q
    simp [Matrix.one_apply]
  simp only [e, Matrix.det_one, one_pow, Finset.prod_const_one] at this
  exact one_ne_zero this

end GlobalTheory.Core.Rk.Top.Model

end
end

