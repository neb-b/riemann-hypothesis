module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.TCover
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.tCover :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → Smooth (eP B j) ∧ Surjective (eP B j) := by
  intro K _ W Z Y q i π D d B T j r hsq
  refine ⟨?_, ?_⟩
  · have hloc : IsZariskiLocalAtSource @Smooth.{0} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
    unfold eP
    exact IsZariskiLocalAtSource.sigmaDesc fun p => inferInstance
  · refine ⟨fun x => ?_⟩
    have hx : r x ∈ i ⁻¹ᵁ (⨆ α, B.V α) := B.cover (Set.mem_univ (r x))
    have hx' : i (r x) ∈ (⨆ α, B.V α) := hx
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    have h3 : π (j x) = i (r x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsq.w]
    have h4 : j x ∈ π ⁻¹ᵁ B.V α := by
      change π (j x) ∈ B.V α
      rw [h3]; exact hα
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp ((B.c α).C_cover h4)
    let p : B.ι × Fin d := (α, k)
    have hp : x ∈ oT B j p := hk
    let y : (oT B j p : Scheme.{0}) := ⟨x, hp⟩
    have hc : tI B j p ≫ eP B j = (oT B j p).ι := by
      unfold tI eP
      exact Sigma.ι_desc _ _
    refine ⟨tI B j p y, ?_⟩
    have hy : (tI B j p ≫ eP B j) y = x := by
      rw [hc]
      rfl
    rw [← Scheme.Hom.comp_apply]
    exact hy
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.USelf
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.uSelf :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k), uV B α k y h k = 1 := by
  intro K _ W Z Y q i π D d B α k V y h
  have hmem : (MvPolynomial.X k - 1 : MvPolynomial (Fin d) Γ(Z, B.V α)) ∈
      RingHom.ker (MvPolynomial.eval₂Hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom) ((B.c α).u k)) := by
    rw [(B.c α).rel k]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hu : (B.c α).u k k = 1 := by
    have h0 := RingHom.mem_ker.mp hmem
    rw [map_sub, map_one, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at h0
    exact sub_eq_zero.mp h0
  unfold uV
  rw [hu, map_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.WCover
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.wCover :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d), Smooth (cP B) ∧ Surjective (cP B) := by
  intro K _ W Z Y q i π D d B
  refine ⟨?_, ⟨fun x => ?_⟩⟩
  · have : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
    unfold cP
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{0}) (fun α => inferInstance)
  · have hx : i x ∈ ⨆ α, B.V α := B.cover (Set.mem_univ x)
    obtain ⟨α, hα⟩ := (TopologicalSpace.Opens.mem_iSup).1 hx
    obtain ⟨y, hy⟩ : x ∈ Set.range (oW B α).ι := by
      rw [Scheme.Opens.range_ι]
      exact hα
    have h : wI B α ≫ cP B = (oW B α).ι := by
      simp [wI, cP]
    refine ⟨wI B α y, ?_⟩
    rw [← Scheme.Hom.comp_apply, h, hy]
end

