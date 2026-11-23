module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem SectionCount.bound_from_one {X : ℝ} {d : ℕ} {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hC
  refine ⟨max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)), fun n hn => ?_⟩
  have hnd : (1 : ℝ) ≤ (n : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hn)
  have hfac : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rcases le_or_gt n₀ n with h | h
  · have h1 := hn₀ n h
    have h2 : C * (n : ℝ) ^ d ≤ max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * (n : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  · have hX : X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤
        |X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ hfac.le
      calc X * (n : ℝ) ^ (d + 1) ≤ |X| * (n : ℝ) ^ (d + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self X) (by positivity)
        _ ≤ |X| * (n₀ : ℝ) ^ (d + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast h.le) _)
              (abs_nonneg X)
    have hM := le_max_right C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ))
    have hM0 : 0 ≤ max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) :=
      le_trans (by positivity) hM
    have h3 := le_mul_of_one_le_right hM0 hnd
    linarith [hf n]

theorem SectionCount.exists_ne_zero_of_isSubvar {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {e : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := k) x) e) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  refine ⟨i, fun h0 => hi ?_⟩
  rw [Kleiman.primeOf, ReciprocityTheory.ChartRestriction.G.Geo.coordIdeal, RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]

theorem SectionCount.transfer (hBase : BaseRealises.Statement)
    (hP : PowRealises.Statement) (hN : NumModel.Statement)
    (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω) (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (Q : Kleiman.LineBundle F x) (ν : K → ℤ)
    (hQ : BundleRealises y k₀ Q ν) (d q : ℕ) (hsub : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) (d + 1)) :
    ((Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun _ : Fin (d + 1) => Q.toSubSystem) -
        ((d + 1 : ℕ) : ℤ) * Kleiman.interNum (Kleiman.primeOf (S := F) x)
          (Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
            (fun _ : Fin d => Q.toSubSystem)) : ℤ) : ℝ) =
      (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) -
        ((d + 1 : ℕ) : ℝ) * (NumbersDVR.intNum F (mIdealOver F y)
          (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) : ℝ) ∧
    ∀ n : ℕ, (Kleiman.twistMul Q.toSubSystem n (-((n : ℤ) * q))).secs =
      secOver F y (n • (ν - q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) := by
  have h1 : Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun _ : Fin (d + 1) => Q.toSubSystem) =
      NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) :=
    hN F K ι Ω y k₀ N e x hx hmod (d + 1) (fun _ => Q) (fun _ => ν) (fun _ => hQ) hsub
  have hqs : ((q : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) = q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    funext j; simp
  have hL : (fun i => (Fin.cons (α := fun _ => Kleiman.LineBundle F x) (Kleiman.twistBundle F x (q : ℤ))
      (fun _ : Fin d => Q) i).toSubSystem) =
      Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
        (fun _ : Fin d => Q.toSubSystem) := by
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  have h2 : Kleiman.interNum (Kleiman.primeOf (S := F) x)
      (Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
        (fun _ : Fin d => Q.toSubSystem)) =
      NumbersDVR.intNum F (mIdealOver F y)
        (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) := by
    rw [NumbersDVR.VerticalDivisorsCommuting.intNum_snoc, ← hL, ← hqs]
    exact hN F K ι Ω y k₀ N e x hx hmod (d + 1) _ (Fin.cons ((q : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) fun _ => ν)
      (fun i => Fin.cases (hBase F K ι Ω y k₀ N e x hx hmod (q : ℤ)) (fun _ => hQ) i) hsub
  refine ⟨by rw [h1, h2]; push_cast; ring, fun n => ?_⟩
  rw [hP F K ι Ω y k₀ N e x hx hmod Q ν hQ n (-((n : ℤ) * q))]
  congr 1
  funext j
  simp only [smul_eq_mul, nsmul_eq_mul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply]
  ring

theorem SectionCount.equiv (hG : GraphModel.Statement) (hB : BundleOfDeg.Statement) (hD : ModelDim.Statement)
    (hBase : BaseRealises.Statement) (hP : PowRealises.Statement) (hV : VeryAmpleModel.Statement)
    (hN : NumModel.Statement) :
    Kleiman.SectionCount.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement := by
  constructor
  · intro hA F _ K _ _ ι _ Ω _ _ y k₀ d ν q hmod hdim hva hq
    have hpos : 0 < Fintype.card (ι k₀) := by
      obtain ⟨i, -⟩ := hmod.1 k₀
      exact Fintype.card_pos_iff.2 ⟨i⟩
    obtain ⟨N, hN'⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    obtain ⟨e⟩ : Nonempty (ι k₀ ≃ Fin (N + 1)) := ⟨(Fintype.equivFin _).trans (finCongr hN')⟩
    obtain ⟨Q, hQ⟩ := hB F K ι Ω y k₀ N e hmod ν
    have hsub := (hD F K ι Ω y k₀ N e _ rfl hmod (d + 1)).2 hdim
    have hvaQ := (hV F K ι Ω y k₀ N e _ rfl hmod Q ν hQ).2 hva
    obtain ⟨hZ, hS⟩ := SectionCount.transfer hBase hP hN F K ι Ω y k₀ N e _ rfl hmod Q ν hQ d q hsub
    obtain ⟨C, hC⟩ := hA F Ω N _ d Q q hsub hvaQ hq
    refine SectionCount.bound_from_one (fun n => Nat.cast_nonneg _) ⟨C, hC.mono fun n hn => ?_⟩
    rw [← hZ, ← hS n]
    exact hn
  · intro hB' k _ Ω _ _ N x d Nb b hsub hva hb
    obtain ⟨r, h, hby⟩ := hva
    have hgen : IsGraphGen Nb 0 h := fun I => by
      rw [Kleiman.SubSystem.twist_twistSys_zero]
      exact hby.generates I
    have hmod := hG k N Ω x Nb 0 (r + 1) h (SectionCount.exists_ne_zero_of_isSubvar hsub) hgen
    have hQ := realises_graph Nb 0 h hgen
    have hdim := (hD k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock N (Equiv.refl _) x rfl
      hmod (d + 1)).1 hsub
    have hvaB := (hV k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock N (Equiv.refl _) x rfl
      hmod Nb (graphDeg 0) hQ).1 ⟨r, h, hby⟩
    obtain ⟨hZ, hS⟩ := SectionCount.transfer hBase hP hN k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω
      (graphVec x h) baseBlock N (Equiv.refl _) x rfl hmod Nb (graphDeg 0) hQ d b hsub
    obtain ⟨C, hC⟩ := hB' k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock d (graphDeg 0) b
      hmod hdim hvaB hb
    refine ⟨C, eventually_atTop.2 ⟨1, fun n hn => ?_⟩⟩
    rw [hZ, hS n]
    exact hC n hn

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def DoubleCech.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (N : ℕ)
    (x : Fin (N + 1) → Ω) (T : Kleiman.SubSystem F x Ω) (B : (∀ k, Finset (ι k)) → Submodule F Ω)
    (M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ j, x j ≠ 0) →
    (∀ I, ¬ CellMeets y I → B I = ⊥) →
    (∀ J I, ¬ CellMeets y I → M J I = ⊥) →
    (∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I) →
    (∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I') →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → CechAugExact F (fun J => M J I) (B I)) →
    (∀ J, CellAugExact F y (M J) ((T.sub J).restrictScalars F)) →
    ∀ n : ℕ, Nonempty (T.H n ≃ₗ[F] cellHOf F y B n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

def RatioDim.Statement : Prop :=
  ∀ (k : Type) [Field k] (N m : ℕ) (W : Ideal (NumbersDVR.MRing (graphIdx N m) k)), W.IsPrime →
    NumbersDVR.IsMultiHomogIdeal W → ∀ j : Fin m,
      (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W →
      (∀ b : Fin m, ∃ f g : Kleiman.Poly k N,
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g ∉ W ∧
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g * X ⟨Sum.inr (), b⟩ -
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f * X ⟨Sum.inr (), j⟩ ∈ W) →
      ringKrullDim (NumbersDVR.MRing (graphIdx N m) k ⧸ W) =
        ringKrullDim (Kleiman.Poly k N ⧸ W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) + 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowChartAct.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (I : ∀ k, Finset (ι k)) (r a : Ω),
    r ∈ Kleiman.chartRing (S := S) (x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J →
    a ∈ cellSec S y γ (baseCell k₀ e J.1 I) → r * a ∈ cellSec S y γ (baseCell k₀ e J.1 I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowSub.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (I : ∀ k, Finset (ι k)),
    (∀ k, (I k).Nonempty) → CellMeets y I →
      chartSecOver S y k₀ e γ J ⊆ cellSec S y γ (baseCell k₀ e J.1 I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowSecGlue.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (a : Ω),
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → a ∈ cellSec S y γ (baseCell k₀ e J.1 fun k => {c k})) →
      a ∈ chartSecOver S y k₀ e γ J

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

def SpanSecs.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (T : Set Ω) (d : ℤ) (s : Ω),
        s ∈ (⨅ I : Kleiman.Chart x,
            (Submodule.span (Kleiman.chartRing F x I) T * Kleiman.twistMod F x d I).restrictScalars F) ↔
          ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
            s * y ⟨k₀, c k₀⟩ ^ (-d) ∈ Submodule.span (chartRingOver F y c) T

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelDim.proof : ModelDim.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n
  subst hx
  exact ModelDimEq.full F K ι Ω y k₀ N e hmod n

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CechContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (Ω : Type) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (G : Kleiman.Chart x → Submodule S Ω) (J₀ : Kleiman.Chart x),
    J₀.1.card = 1 →
    (∀ J J' : Kleiman.Chart x, J.1 ⊆ J'.1 → G J ≤ G J') →
    (∀ J J' : Kleiman.Chart x, J'.1 = J₀.1 ∪ J.1 → G J' = G J) →
    CechAugExact S G (G J₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CellZeroConst.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω),
    cellD S y 0 s = 0 →
      ∀ c c' : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, CellMeets y c.1 → CellMeets y c'.1 → s c = s c'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PBundlePair
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

noncomputable section

section FirstTyping

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem twist_sub_eq_mul (F Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, w, hw, rfl⟩
    exact ⟨q, hq, w, hw, rfl⟩
  · rintro ⟨q, hq, w, hw, rfl⟩
    exact ⟨q, hq, w, hw, rfl⟩

theorem exists_mul_eq_prod_pow {I : Finset (Fin (N + 1))} {s : Kleiman.Poly S N} (hs : s ∈ Kleiman.monos I) :
    ∃ (r d d' : ℕ) (s' : Kleiman.Poly S N), s.IsHomogeneous d ∧ s'.IsHomogeneous d' ∧
      d + d' = r * I.card ∧ s * s' = (∏ j ∈ I, X j) ^ r := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    have hj' : j ∈ I := by exact_mod_cast hj
    refine ⟨1, 1, (I.erase j).card, ∏ l ∈ I.erase j, X l, isHomogeneous_X S j, ?_, ?_, ?_⟩
    · simpa using IsHomogeneous.prod (I.erase j) (fun l => (X l : Kleiman.Poly S N)) (fun _ => 1)
        (fun l _ => isHomogeneous_X S l)
    · rw [one_mul, add_comm]
      exact Finset.card_erase_add_one hj'
    · rw [pow_one]
      exact Finset.mul_prod_erase I (fun l => (X l : Kleiman.Poly S N)) hj'
  | one => exact ⟨0, 0, 0, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨r, d, d', s', h1, h2, h3, h4⟩ := ha
    obtain ⟨r₂, d₂, d₂', t', g1, g2, g3, g4⟩ := hb
    refine ⟨r + r₂, d + d₂, d' + d₂', s' * t', h1.mul g1, h2.mul g2, by rw [add_mul]; omega, ?_⟩
    rw [pow_add, ← h4, ← g4]
    ring

theorem mem_sub_iff_gam (Q : Kleiman.LineBundle S x) (I : Kleiman.Chart x) (t : Ω) :
    t ∈ Q.sub I ↔ ∃ n : ℕ, Kleiman.xProd I ^ n * t ∈ Q.gam ((n * I.1.card : ℕ) : ℤ) := by
  classical
  have hxI : Kleiman.xProd I ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => (Kleiman.mem_support x).mp (I.2.2 hi)
  have hprod : ∀ r : ℕ, aeval x ((∏ j ∈ I.1, (X j : Kleiman.Poly S N)) ^ r) = Kleiman.xProd I ^ r := by
    intro r
    simp [Kleiman.xProd, map_prod]
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
    have hsub : (Kleiman.singleChart hxi).1 ⊆ I.1 := Finset.singleton_subset_iff.mpr hi
    obtain ⟨a, ⟨u, hu⟩, hat⟩ := (Q.mem_iff _ I hsub t).mp ht
    have hev : ∀ᶠ n : ℕ in Filter.atTop, ∀ J, x i ^ n • ((a : Ω) • t) ∈
        (Q.twist (Kleiman.twistSys S x (n : ℤ))).sub J :=
      Filter.eventually_all.mpr fun J =>
        Kleiman.ExtensionProof.eventually_pow_smul_mem Q.toSubFamily hxi hat J
    obtain ⟨n, hn⟩ := hev.exists
    have hgam : x i ^ n • ((a : Ω) • t) ∈ Q.gam (n : ℤ) := Kleiman.ExtensionProof.mem_gam.mpr hn
    have hinv : (a : Ω) * ((↑u⁻¹ : Kleiman.chartRing S x I) : Ω) = 1 := by
      have := congrArg Subtype.val (Units.mul_inv u)
      rw [hu] at this
      exact this
    obtain ⟨g, s, r, hs, hg, hsr, hb⟩ := (↑u⁻¹ : Kleiman.chartRing S x I).2
    obtain ⟨r', d, d', s', hsd, hs', hdd, hss⟩ := exists_mul_eq_prod_pow hs
    have hs0 : aeval x s ≠ 0 := Kleiman.eval_ne_zero_of_mem_monos I hs
    have hrd : r = d := hsr.inj_right hsd (fun h => hs0 (by rw [h, map_zero]))
    subst hrd
    have h1 : (∏ l ∈ I.1.erase i, (X l : Kleiman.Poly S N)).IsHomogeneous (I.1.erase i).card := by
      simpa using IsHomogeneous.prod (I.1.erase i) (fun l => (X l : Kleiman.Poly S N)) (fun _ => 1)
        (fun l _ => isHomogeneous_X S l)
    have hPh := ((h1.pow n).mul hg).mul hs'
    have hmem := Kleiman.ExtensionProof.smul_mem_gam Q.toSubSystem hPh hgam
    refine ⟨n + r', ?_⟩
    have hc := Finset.card_erase_add_one hi
    have hdeg : ((n : ℤ) + (((I.1.erase i).card * n + r + d' : ℕ) : ℤ)) =
        (((n + r') * I.1.card : ℕ) : ℤ) := by
      rw [← hc] at hdd ⊢
      have hdd' : ((r : ℤ) + d') = r' * ((I.1.erase i).card + 1) := by exact_mod_cast hdd
      push_cast
      linear_combination hdd'
    rw [hdeg] at hmem
    convert hmem using 1
    have hag : (a : Ω) * aeval x g = aeval x s := by
      rw [hb] at hinv
      field_simp at hinv
      linear_combination hinv
    have hss' : aeval x s * aeval x s' = (x i * ∏ l ∈ I.1.erase i, x l) ^ r' := by
      have := congrArg (aeval x) hss
      simp only [map_mul, map_pow, map_prod, aeval_X] at this
      rw [this, Finset.mul_prod_erase I.1 x hi]
    simp only [smul_eq_mul, map_mul, map_pow, map_prod, aeval_X, Kleiman.xProd]
    rw [← Finset.mul_prod_erase I.1 x hi]
    linear_combination (-(x i * ∏ l ∈ I.1.erase i, x l) ^ n * t) * hss' +
      (-(x i * ∏ l ∈ I.1.erase i, x l) ^ n * t * aeval x s') * hag
  · rintro ⟨n, hn⟩
    have h1 := (Kleiman.ExtensionProof.mem_gam.mp hn) I
    have hs : (∏ j ∈ I.1, (X j : Kleiman.Poly S N)) ^ n ∈ Kleiman.monos I.1 :=
      pow_mem (prod_mem fun j hj => Kleiman.X_mem_monos hj) n
    have hsh : ((∏ j ∈ I.1, (X j : Kleiman.Poly S N)) ^ n).IsHomogeneous (I.1.card * n) := by
      have := IsHomogeneous.prod I.1 (fun l => (X l : Kleiman.Poly S N)) (fun _ => 1)
        (fun l _ => isHomogeneous_X S l)
      simpa using this.pow n
    have h2 := Kleiman.ExtensionProof.inv_smul_mem Q.toSubSystem h1 hs hsh (by push_cast; ring)
    rw [hprod, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hxI), one_mul] at h2
    exact h2

end FirstTyping

section SecondTyping

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra S Ω]

theorem mem_secOver_iff_charts (y : (Σ k, ι k) → Ω) (δ : K → ℤ) (t : Ω) :
    t ∈ secOver S y δ ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      t * ∏ k, y ⟨k, c k⟩ ^ (-δ k) ∈ chartRingOver S y c := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]

end SecondTyping

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

