module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellDMulLeft
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem cellD_mul_left (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : ℕ) (r : Ω)
    (t : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :
    cellD S y n (fun I => r * t I) = fun J => r * cellD S y n t J := by
  classical
  funext J
  simp only [cellD, LinearMap.pi_apply]
  split_ifs with hJ
  · simp only [LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul_comm]
      rfl
    · simp
  · simp

theorem CellLocGlue.proof : CellLocGlue.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y G R m f u hf hu hsum hR hloc q s hs hds
  classical
  have memC : ∀ (H : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) (x : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω),
      x ∈ cellCOf S H n ↔ ∀ I, x I ∈ H I.1 := fun H n x => by
    simp [cellCOf, Submodule.mem_pi]

  let J : Ideal R :=
    { carrier := {r | ∃ t ∈ cellCOf S G q, cellD S y q t = fun I => (r : Ω) * s I}
      add_mem' := by
        rintro a b ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        refine ⟨ta + tb, Submodule.add_mem _ hta htb, ?_⟩
        rw [map_add (f := _), ha, hb]
        funext I
        simp [add_mul]
      zero_mem' := ⟨0, Submodule.zero_mem _, by funext I; simp⟩
      smul_mem' := by
        rintro c a ⟨t, ht, hdt⟩
        refine ⟨fun I => (c : Ω) * t I, (memC _ _ _).2 fun I => hR _ _ c.2 _ ((memC _ _ _).1 ht I), ?_⟩
        rw [cellD_mul_left, hdt]
        funext I
        simp [mul_assoc] }

  have hmono : ∀ l (I : ∀ k, Finset (ι k)),
      Monotone fun n : ℕ => (G I).comap (LinearMap.mulLeft S (f l ^ n)) := by
    intro l I n n' hnn' a ha
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at ha ⊢
    have : f l ^ n' * a = f l ^ (n' - n) * (f l ^ n * a) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnn']
    rw [this]
    exact hR _ _ (pow_mem (hf l) _) _ ha
  have key : ∀ l, ∃ N : ℕ, (⟨f l, hf l⟩ : R) ^ N ∈ J := by
    intro l
    have hsl : s ∈ cellCOf S (cellLocSys G (f l)) (q + 1) := by
      rw [memC] at hs ⊢
      intro I
      exact (le_iSup (fun n : ℕ => (G I.1).comap (LinearMap.mulLeft S (f l ^ n))) 0)
        (by simpa [Submodule.mem_comap] using hs I)
    obtain ⟨t, ht, hdt⟩ := hloc l q s hsl hds
    have hn : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q, ∃ n : ℕ, f l ^ n * t I ∈ G I.1 := by
      intro I
      have h := (memC _ _ _).1 ht I
      rw [cellLocSys, Submodule.mem_iSup_of_directed _ (hmono l I.1).directed_le] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n, by simpa [Submodule.mem_comap] using hn⟩
    choose n hn using hn
    have : Finite (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q) := by unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell; infer_instance
    have : Fintype (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q) := Fintype.ofFinite _
    refine ⟨Finset.univ.sup n, fun I => f l ^ Finset.univ.sup n * t I, (memC _ _ _).2 fun I => ?_, ?_⟩
    · have := hmono l I.1 (Finset.le_sup (Finset.mem_univ I) : n I ≤ Finset.univ.sup n)
      exact this (by simpa [Submodule.mem_comap] using hn I)
    · rw [cellD_mul_left, hdt]
      funext I
      simp
  have hone : (1 : R) ∈ J := by
    have hrad : J.radical = ⊤ := by
      rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
      have h1 : (1 : R) = ∑ l, (⟨u l, hu l⟩ : R) * ⟨f l, hf l⟩ :=
        Subtype.ext (by simpa using hsum.symm)
      rw [h1]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (key l)
    rw [Ideal.radical_eq_top] at hrad
    rw [hrad]
    exact Submodule.mem_top
  obtain ⟨t, ht, hdt⟩ := hone
  exact ⟨t, ht, by rw [hdt]; funext I; simp⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPtZeroNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def ModelNumEq.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (d : ℕ) (βs : Fin d → K → ℤ)
      (Qs : Fin d → Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ j (c : ℤ), ((Qs j).twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (βs j + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
          (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) d →
      Kleiman.interNum (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
          (fun j => (Qs j).toSubSystem) =
        NumbersDVR.intNum F (mIdealOver F y) βs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def ModelVeryAmpleEq.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      ∀ (a : ℕ) (m : ℤ), 1 ≤ a →
        (Kleiman.IsVeryAmple (Kleiman.twistMul Q.toSubSystem a m) ↔
          IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver cechHc quotPart)

def ModelCechTwist.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      ∀ (p b : ℕ) (m c : ℤ) (i : ℕ),
        Nonempty ((((Kleiman.twistMul Q.toSubSystem p m).pow b).twist
            (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).H i ≃ₗ[F]
          cechHc ι (quotPart F (mIdealOver F y)) (b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β p m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) i)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def ModelChangeNef.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      (IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y' β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def ModelMulSecs.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      ∀ (p : ℕ) (j : ℤ), (Kleiman.twistMul Q.toSubSystem p j).secs =
        secOver F y (p • β + j • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def TensorRealises.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
    ∀ (L L' : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (β β' : K → ℤ),
      BundleRealises y k₀ L β → BundleRealises y k₀ L' β' → BundleRealises y k₀ (L.tensor L') (β + β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowLocCover.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      ∃ (m : ℕ) (f u : Fin m → Ω),
        (∀ l, f l ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) ∧
        (∀ l, u l ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) ∧
        ∑ l, u l * f l = 1 ∧
        ∀ l, ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧
          (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I →
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I = ⊥) ∧
          (∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' →
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I ≤
              cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I') ∧
          (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l)
                (Function.update I k (insert (c k) (I k))) =
              cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

theorem ModelGenerated.proof : ModelGenerated.Statement := by
  classical
  intro F _ K _ _ ι _ Ω _ _ y k₀ hy β
  obtain ⟨i₀, -⟩ := hy.1 k₀
  have hcard : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hcard).symm⟩
  let e : ι k₀ ≃ Fin (N + 1) := (Fintype.equivFin _).trans (finCongr hN)
  set x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm with hx
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hy β
  obtain ⟨c₀, hc₀⟩ := Kleiman.Generated.full.{0, 0} F Ω N x Q
  refine ⟨c₀, fun c hc => ?_⟩
  set δ := β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ with hδ
  set L := Q.tensor (Kleiman.twistBundle F x c) with hL
  have hLsys : L.toSubSystem = Q.toSubSystem.twist (Kleiman.twistSys F x c) := rfl
  have hgen : L.toSubSystem.Generated := by rw [hLsys]; exact hc₀ c hc
  have hsecs : L.toSubSystem.secs = secOver F y δ := by rw [hLsys, hQ c]

  have hgam : ∀ m : ℤ, L.toSubSystem.gam m = secOver F y (δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro m
    rw [Kleiman.SubSystem.gam, hLsys, Kleiman.SubSystem.twist_assoc, Kleiman.twistSys_twist_twistSys, hQ (c + m),
      hδ, add_smul, add_assoc]

  have hsub : ∀ I : Kleiman.Chart x, (L.sub I : Set Ω) = chartSecOver F y k₀ e δ I := by
    intro I
    ext t
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [hgam]

  have hfg : ∀ I : Kleiman.Chart x, ∃ G : Finset Ω, Submodule.span (Kleiman.chartRing F x I) (G : Set Ω) = L.sub I :=
    fun I => L.fg I
  choose G hG using hfg
  have hfin : ∀ (I : Kleiman.Chart x) (g : Ω), ∃ T : Finset Ω, (T : Set Ω) ⊆ L.toSubSystem.secs ∧
      (g ∈ L.sub I → g ∈ Submodule.span (Kleiman.chartRing F x I) (T : Set Ω)) := by
    intro I g
    by_cases hg : g ∈ L.sub I
    · rw [← hgen I] at hg
      obtain ⟨T, hT, hgT⟩ := Submodule.mem_span_finite_of_mem_span hg
      exact ⟨T, hT, fun _ => hgT⟩
    · exact ⟨∅, by simp, fun h => absurd h hg⟩
  choose T hTsec hTspan using hfin
  let U : Finset Ω := Finset.univ.biUnion fun I => (G I).biUnion fun g => T I g
  have hU : (U : Set Ω) ⊆ L.toSubSystem.secs := by
    intro s hs
    simp only [U, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
      Finset.mem_coe] at hs
    obtain ⟨I, g, -, hs⟩ := hs
    exact hTsec I g hs
  have hspanU : ∀ I : Kleiman.Chart x, Submodule.span (Kleiman.chartRing F x I) (U : Set Ω) = L.sub I := by
    intro I
    apply le_antisymm
    · rw [← hgen I]
      exact Submodule.span_mono hU
    · rw [← hG I, Submodule.span_le]
      intro g hg
      have hgI : g ∈ L.sub I := by rw [← hG I]; exact Submodule.subset_span hg
      refine Submodule.span_mono ?_ (hTspan I g hgI)
      intro s hs
      simp only [U, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
        Finset.mem_coe]
      exact ⟨I, g, hg, hs⟩
  let η : Fin U.card → Ω := fun j => (U.equivFin.symm j : Ω)
  have hrange : Set.range η = (U : Set Ω) := by
    ext s
    constructor
    · rintro ⟨j, rfl⟩
      exact (U.equivFin.symm j).2
    · intro hs
      exact ⟨U.equivFin ⟨s, hs⟩, by simp [η]⟩
  have hη : ∀ j, η j ∈ secOver F y δ := fun j => hsecs ▸ hU (hrange ▸ Set.mem_range_self j)
  refine ⟨U.card, η, hη, ?_⟩
  refine (ChartSecGen.full F K ι Ω y k₀ N e hy δ U.card η hη).mpr fun I => ?_
  rw [hrange, hspanU I, hsub I]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveNumModel.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
      ∀ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W →
        relDim W = ((1 : ℕ) : WithBot (WithTop ℤ)) →
        NumbersDVR.intNum F W ![β] =
          Kleiman.interNum (W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k))) ![Q.toSubSystem]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

