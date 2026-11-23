module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusId

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsReindexFin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowGerm.UnivConv

variable {V : Type} [CommRing V]

def toAt (A : Type) [CommRing A] [Algebra V A] : Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A :=
  Over.homMk (𝟙 _) (by simp)

def ofAt (A : Type) [CommRing A] [Algebra V A] : overAt (𝟙 (Sp V)) A ⟶ Chart.sp (R₀ := V) A :=
  Over.homMk (𝟙 _) (by simp)

theorem toAt_ofAt (A : Type) [CommRing A] [Algebra V A] : toAt (V := V) A ≫ ofAt A = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

theorem ofAt_toAt (A : Type) [CommRing A] [Algebra V A] : ofAt (V := V) A ≫ toAt A = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

theorem spMap_toAt {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) :
    Chart.spMap f ≫ toAt A = toAt B ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f :=
  Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem ofAt_spMap {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) :
    ofAt B ≫ Chart.spMap f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) f ≫ ofAt A :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

def ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv V β) (by
    rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp, orig]
    congr 2
    ext p
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨β.symm k, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ⟨β i, by simp⟩)

theorem ren_zR {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) (i : Fin N) :
    ren (V := V) β m (Chart.zR m i) = Ideal.Quotient.mk _ (MvPolynomial.X (β i)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.rename β (MvPolynomial.X i)) = _
  rw [MvPolynomial.rename_X]

theorem aug_ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (jetAug : Jet V κ m →ₐ[V] V).comp (ren (V := V) β m).toAlgHom = Chart.jetAug V (Fin N) m :=
  Chart.jet_ext fun j => by
    rw [Chart.jetAug_zR]
    show jetAug (ren (V := V) β m (Chart.zR m j)) = 0
    rw [ren_zR]
    show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X (β j)) = 0
    simp

theorem trunc_ren {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m).comp (ren (V := V) β (m + 1)).toAlgHom =
      (ren (V := V) β m).toAlgHom.comp (Chart.jetTruncR V (Fin N) m) :=
  Chart.jet_ext fun j => rfl

theorem aug_symm {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (Chart.jetAug V (Fin N) m).comp (ren (V := V) β m).symm.toAlgHom = jetAug := by
  rw [← aug_ren β m]
  exact AlgHom.ext fun a => by simp

theorem trunc_symm {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (m : ℕ) :
    (Chart.jetTruncR V (Fin N) m).comp (ren (V := V) β (m + 1)).symm.toAlgHom =
      (ren (V := V) β m).symm.toAlgHom.comp (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) :=
  AlgHom.ext fun a => by
    obtain ⟨b, rfl⟩ := (ren (V := V) β (m + 1)).surjective a
    have h : jetTrunc (ren (V := V) β (m + 1) b) = ren (V := V) β m (Chart.jetTruncR V (Fin N) m b) :=
      AlgHom.congr_fun (trunc_ren (V := V) β m) b
    show Chart.jetTruncR V (Fin N) m ((ren (V := V) β (m + 1)).symm (ren (V := V) β (m + 1) b)) =
      (ren (V := V) β m).symm (jetTrunc (ren (V := V) β (m + 1) b))
    rw [h, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]

theorem zero_eq (N m : ℕ) : Chart.jetZeroR V (Fin N) m =
    (Algebra.ofId V (Chart.JetR V (Fin N) 0)).comp (Chart.jetAug V (Fin N) m) :=
  Chart.jet_ext fun j => by
    rw [AlgHom.comp_apply, Chart.jetAug_zR, map_zero]
    show Ideal.Quotient.mk _ (MvPolynomial.X j) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
    exact Ideal.subset_span ⟨j, rfl⟩

end GlobalTheory.PowGerm.UnivConv

namespace GlobalTheory.PowGerm
open UnivConv

theorem univConv : UnivConvSt := by
  intro V _ G _ κ z hz N β
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun m => Chart.spMap (ren (V := V) β m).symm.toAlgHom ≫ toAt _ ≫ z m, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro m
    rw [← Category.assoc, Chart.spMap_comp, trunc_symm, ← Chart.spMap_comp, Category.assoc,
      ← Category.assoc (Chart.spMap jetTrunc), spMap_toAt, Category.assoc, h1]
  · intro m
    rw [← Category.assoc, Chart.spMap_comp, zero_eq, AlgHom.comp_assoc, aug_symm, ← Chart.spMap_comp, Category.assoc,
      ← Category.assoc (Chart.spMap jetAug), spMap_toAt, Category.assoc, h2, ← Category.assoc]
    exact MonObj.comp_one _
  · intro A _ _ aug m hm y hy
    obtain ⟨φ, ⟨hφ1, hφ2⟩, hu⟩ := h3 A aug m hm (ofAt A ≫ y) (by
      rw [← Category.assoc, ← ofAt_spMap, Category.assoc, hy]
      exact MonObj.comp_one _)
    refine ⟨φ.comp (ren (V := V) β m).toAlgHom, ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hφ1, aug_ren]
    · have e : (φ.comp (ren (V := V) β m).toAlgHom).comp (ren (V := V) β m).symm.toAlgHom = φ :=
        AlgHom.ext fun a => by simp
      rw [← Category.assoc, Chart.spMap_comp, e, ← Category.assoc, spMap_toAt, Category.assoc, ← hφ2,
        ← Category.assoc, toAt_ofAt, Category.id_comp]
    · rintro ψ ⟨hψ1, hψ2⟩
      have e := hu (ψ.comp (ren (V := V) β m).symm.toAlgHom) ⟨by rw [← AlgHom.comp_assoc, hψ1, aug_symm], by
        rw [hψ2, ← Category.assoc (Chart.spMap ψ), Chart.spMap_comp, ← Category.assoc, ofAt_spMap, Category.assoc,
          ← Category.assoc (ofAt _), ofAt_toAt, Category.id_comp]⟩
      rw [← e]
      exact AlgHom.ext fun a => by simp
  · intro m
    refine ⟨ren β m, ren_zR β m, ?_⟩
    have e : Chart.spMap (ren (V := V) β m).toAlgHom ≫
        Chart.spMap (ren (V := V) β m).symm.toAlgHom ≫ toAt _ ≫ z m = toAt _ ≫ z m := by
      have e' : (ren (V := V) β m).toAlgHom.comp (ren (V := V) β m).symm.toAlgHom = AlgHom.id V _ :=
        AlgHom.ext fun a => by simp
      have e'' : Chart.spMap (AlgHom.id V (Jet V κ m)) = 𝟙 _ :=
        Over.OverMorphism.ext (Spec.map_id _)
      rw [← Category.assoc, Chart.spMap_comp, e', e'', Category.id_comp]
    exact (Category.id_comp _).symm.trans (congrArg CommaMorphism.left e).symm

end GlobalTheory.PowGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordLDecompositionNfSpan
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.WordL

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem mem_of_bmon (d : Q.NFData P A) {b : A} (hb : b ∈ bmon d) : b ∈ nfSpan d ∅ 0 0 0 :=
  Submodule.subset_span ⟨b, hb, [], rfl, by simp, by simp⟩

theorem span_eq (d : Q.NFData P A) : nfSpan d ∅ 0 0 0 = Submodule.span ℂ (bmon d : Set A) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨b, hb, H, hH, -, rfl⟩
    rw [List.length_eq_zero_iff.mp hH]
    simpa using Submodule.subset_span (R := ℂ) (s := (bmon d : Set A)) hb
  · exact Submodule.span_le.mpr fun b hb => mem_of_bmon d hb

theorem span_mul (d : Q.NFData P A) {x y : A} (hx : x ∈ nfSpan d ∅ 0 0 0) (hy : y ∈ nfSpan d ∅ 0 0 0) :
    x * y ∈ nfSpan d ∅ 0 0 0 := by
  rw [span_eq] at *
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact (bmon d).mul_mem ha hb

theorem kappa_mem (d : Q.NFData P A) (f : M.Ty P → ℂ) : d.κ f ∈ nfSpan d ∅ 0 0 0 :=
  mem_of_bmon d (Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩))))

theorem zbi_mem (d : Q.NFData P A) : d.L.ζbi ∈ nfSpan d ∅ 0 0 0 :=
  mem_of_bmon d (Submonoid.subset_closure (Or.inl (Or.inl (Or.inl (by simp)))))

variable {S : Type} [Fintype S] [DecidableEq S]

def BMat (d : Q.NFData P A) (E : SlopeTestRemainingChoices S A) : Prop := ∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0

theorem BMat.mul {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E * F) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Submodule.sum_mem _ fun k _ => span_mul d (hE i k) (hF k j)

theorem BMat.add {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E + F) :=
  fun i j => add_mem (hE i j) (hF i j)

theorem BMat.sub {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E - F) :=
  fun i j => sub_mem (hE i j) (hF i j)

theorem BMat.smul {d : Q.NFData P A} {E : SlopeTestRemainingChoices S A} (c : ℂ) (hE : BMat d E) : BMat d (c • E) :=
  fun i j => Submodule.smul_mem _ c (hE i j)

theorem bMat_io {d : Q.NFData P A} {a : A} (ha : a ∈ nfSpan d ∅ 0 0 0) : BMat d (io a : SlopeTestRemainingChoices S A) := fun i j => by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact zero_mem _

theorem io_add (a b : A) : (io (a + b) : SlopeTestRemainingChoices S A) = io a + io b := map_add (Matrix.scalar (Ix S)) a b

theorem io_mul (a b : A) : (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b := map_mul (Matrix.scalar (Ix S)) a b

theorem inv_subset {r : ℕ} (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) :
    ∀ Y ∈ (ofWord L st w).inv, Y ∈ st.inv := by
  induction w with
  | nil => exact fun Y hY => hY
  | cons l w ih =>
    intro Y hY
    by_cases hp : l.plus
    · have e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e] at hY
      exact ih Y hY.1
    · have e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e] at hY
      exact ih Y hY.1

theorem comm_id {R : Type*} [Ring R] (l K E α β γ : R) (h1 : β * l = l * β) (h2 : β * K = K * β)
    (h3 : α * K = K * α) :
    α * ((l + K * E) * β - β * (l + K * E)) * γ = K * (α * (E * β - β * E) * γ) := by
  have : (l + K * E) * β - β * (l + K * E) = K * (E * β - β * E) := by
    rw [mul_add, h1, ← mul_assoc β K, h2]; noncomm_ring
  rw [this, ← mul_assoc α K, h3]; simp only [mul_assoc]

end

theorem word_l_shape : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).l L Y = io (d.L.l0 Y) + kapL d.L * E := by
  intro P A _ _ _ _ d hd L st s hT S _ _ w hA Y hY hY1
  obtain ⟨hk, h0⟩ := _root_.GlobalTheory.HatNF.start_normalForm P A d hd L st s hT
  obtain ⟨E0, hE0, e0⟩ := h0 Y (inv_subset L st w Y hY)
  obtain ⟨hH, hS, -⟩ := hT
  obtain ⟨-, -, -, -, -, -, -, s1, s2, s3, -, s4, s5⟩ := hS
  have hkap : (kapL L : SlopeTestRemainingChoices S A) = kapL d.L := by simp only [kapL, s1, s2, s4]
  have htz : (tz L : SlopeTestRemainingChoices S A) = tz d.L := by simp only [tz, s3, s5]
  have hl0 : (st.frame : FrameData S A).l L Y = io (d.L.l0 Y) + kapL d.L * io E0 := by
    show io (L.l0 Y) + io (L.ζb * L.ζi * L.GGi) * io (st.ee Y) =
      io (d.L.l0 Y) + io (d.L.ζb * d.L.ζi * d.L.GGi) * io E0
    rw [← io_mul, ← io_add, e0, io_add, io_mul]
  have hsh := (Formalism.FourierDecayAlt.P.l_shape A S P.r L st w hH.starLev hH.start hA).2.2 Y hY hY1
  rw [hl0, hkap, htz] at hsh
  have hc := hd.2.2.1.2.1
  have cζb : ∀ f, Commute (d.κ f) d.L.ζb := fun f => hc f _ (by simp [LevelData.fns])
  have cζi : ∀ f, Commute (d.κ f) d.L.ζi := fun f => hc f _ (by simp [LevelData.fns])
  have cG : ∀ f, Commute (d.κ f) d.L.GGi := fun f => hc f _ (by simp [LevelData.fns])
  have cn : ∀ f, Commute (d.κ f) d.L.nab := fun f => hc f _ (by simp)
  have cio : ∀ (a : A), (∀ f, Commute (d.κ f) a) → ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * io a = io a * α := by
    intro a ha α hα
    refine (Formalism.FourierDecayAlt.P.TLA.L1.io_comm fun i j => ?_).symm.eq
    obtain ⟨f, hf⟩ := hk _ (hα i j)
    rw [← hf]; exact (ha f).symm
  have cK : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * kapL d.L = kapL d.L * α :=
    cio _ fun f => ((cζb f).mul_right (cζi f)).mul_right (cG f)
  have cl : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * io (d.L.l0 Y) = io (d.L.l0 Y) * α :=
    cio _ fun f => (cn f).neg_right.sub_right
      ((show Commute (d.κ f) (algebraMap ℂ A (Y + 1 / 2)) from (Algebra.commutes _ _).symm).mul_right
        ((cζb f).mul_right (cG f)))
  have hB : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → BMat d α := by
    intro α hα i j
    obtain ⟨f, hf⟩ := hk _ (hα i j)
    rw [← hf]; exact kappa_mem d f
  have hE : BMat d (io E0 : SlopeTestRemainingChoices S A) := bMat_io hE0
  have key : ∀ M ∈ TL.dSpan st (io (d.L.l0 Y) + kapL d.L * io E0 : SlopeTestRemainingChoices S A) (kapL d.L) (tz d.L),
      ∃ E : SlopeTestRemainingChoices S A, BMat d E ∧ M = kapL d.L * E := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨α, β, γ, h1, h2, h3, rfl⟩ | ⟨γ, h, rfl | rfl⟩
      · exact ⟨_, ((hB α h1).mul ((hE.mul (hB β h2)).sub ((hB β h2).mul hE))).mul (hB γ h3),
          comm_id _ _ _ _ _ _ (cl β h2) (cK β h2) (cK α h1)⟩
      · exact ⟨γ, hB γ h, rfl⟩
      · exact ⟨tz d.L * γ, (bMat_io (Submodule.smul_mem _ _ (zbi_mem d))).mul (hB γ h), mul_assoc _ _ _⟩
    | zero => exact ⟨0, fun _ _ => zero_mem _, (mul_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨E, hE, rfl⟩ := hx
      obtain ⟨F, hF, rfl⟩ := hy
      exact ⟨E + F, hE.add hF, (mul_add _ _ _).symm⟩
    | smul c x _ hx =>
      obtain ⟨E, hE, rfl⟩ := hx
      exact ⟨c • E, hE.smul c, (mul_smul_comm _ _ _).symm⟩
  obtain ⟨E, hE', e⟩ := key _ hsh
  refine ⟨io E0 + E, hE.add hE', ?_⟩
  rw [sub_eq_iff_eq_add.mp e, mul_add]
  abel

end GlobalTheory.HatNF.WordL
end

