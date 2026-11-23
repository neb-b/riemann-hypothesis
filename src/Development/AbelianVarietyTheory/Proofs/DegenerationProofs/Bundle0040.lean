module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescends
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ExtDescent

variable {S S₀ : Scheme.{0}} {f : S ⟶ S₀}

theorem hom_ext_of_points [Flat f] [Surjective f] {X Y : Over S₀} {a b : X ⟶ Y}
    (h : ∀ (T : Over S) (t : Over.mk (T.hom ≫ f) ⟶ X), t ≫ a = t ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  haveI := Flat.epi_of_flat_of_surjective (pullback.fst X.hom f)
  rw [← cancel_epi (pullback.fst X.hom f)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom f))
    (Over.homMk (pullback.fst X.hom f) (by simpa using pullback.condition)))

theorem isMonHom_of_grpPullback [Flat f] [Surjective f] {X Y : Over S} {X₀ Y₀ : Over S₀}
    [GrpObj X] [GrpObj Y] [GrpObj X₀] [GrpObj Y₀] {φ : X.left ⟶ X₀.left} {ψ : Y.left ⟶ Y₀.left}
    (hX : IsGrpPullback X X₀ f φ) (hY : IsGrpPullback Y Y₀ f ψ) (g : X ⟶ Y) (g₀ : X₀ ⟶ Y₀)
    (w : φ ≫ g₀.left = g.left ≫ ψ) [IsMonHom g] : IsMonHom g₀ := by
  have pa : ∀ {T : Over S} (x : T ⟶ X), pushHom hX T x ≫ g₀ = pushHom hY T (x ≫ g) := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, w, Category.assoc])
  have hm : μ[X₀] ≫ g₀ = (g₀ ⊗ₘ g₀) ≫ μ := by
    refine hom_ext_of_points (f := f) fun T t => ?_
    obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective hX.1 T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective hX.1 T (t ≫ snd _ _)
    obtain rfl : t = lift (pushHom hX T x) (pushHom hX T y) :=
      CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst]; exact hx.symm)
        (by rw [lift_snd]; exact hy.symm)
    rw [← Category.assoc, ← Hom.mul_def, ← map_mul, pa, lift_map_assoc, ← Hom.mul_def, pa, pa,
      ← map_mul, MonObj.mul_comp]
  refine ⟨?_, hm⟩
  have e : (η[X₀] ≫ g₀) * (η[X₀] ≫ g₀) = η[X₀] ≫ g₀ := by
    rw [Hom.mul_def, ← lift_map, Category.assoc, ← hm, ← Category.assoc]
    congr 1
    simpa [Hom.mul_def, Hom.one_def] using _root_.mul_one (1 : 𝟙_ (Over S₀) ⟶ X₀)
  have e' : η[X₀] ≫ g₀ = 1 := by simpa using e
  rw [e', Hom.one_def]; simp

theorem unit_comm {X : Over S} {X₀ : Over S₀} [GrpObj X] [GrpObj X₀] {φ : X.left ⟶ X₀.left}
    (h : IsGrpPullback X X₀ f φ) : f ≫ (η[X₀]).left = (η[X]).left ≫ φ := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S))))
  have e₁ : (1 : 𝟙_ (Over S) ⟶ X) = η[X] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine Eq.symm (e.trans ?_)
  show (toUnit _ ≫ η[X₀]).left = _
  simp

theorem fpqc_of_isPullback [Flat f] [Surjective f] [QuasiCompact f] {X X₀ : Scheme.{0}} {p : X ⟶ X₀}
    {s : X ⟶ S} {s₀ : X₀ ⟶ S₀} (h : IsPullback p s s₀ f) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) p :=
  ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›,
    MorphismProperty.of_isPullback (P := @Flat) h.flip ‹_›⟩,
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip ‹_›⟩

theorem isPullback_of_baseChange [Flat f] [Surjective f] [QuasiCompact f] {T G B T₀ G₀ B₀ : Scheme.{0}}
    {i : T ⟶ G} {t : T ⟶ S} {q : G ⟶ B} {e : S ⟶ B} (H : IsPullback i t q e)
    {i₀ : T₀ ⟶ G₀} {t₀ : T₀ ⟶ S₀} {q₀ : G₀ ⟶ B₀} {e₀ : S₀ ⟶ B₀}
    {τ : T ⟶ T₀} {g : G ⟶ G₀} {φ : B ⟶ B₀} (hτ : IsPullback τ t t₀ f) (hγ : IsPullback g q q₀ φ)
    (hi : τ ≫ i₀ = i ≫ g) (he : f ≫ e₀ = e ≫ φ) : IsPullback i₀ t₀ q₀ e₀ := by
  haveI : Flat τ := (fpqc_of_isPullback hτ).1.2
  haveI : Surjective τ := (fpqc_of_isPullback hτ).1.1
  haveI := Flat.epi_of_flat_of_surjective τ
  have w : i₀ ≫ q₀ = t₀ ≫ e₀ := by
    rw [← cancel_epi τ, reassoc_of% hi, hγ.w, reassoc_of% H.w, reassoc_of% hτ.w, he]
  let c : T₀ ⟶ pullback q₀ e₀ := pullback.lift i₀ t₀ w
  have c₁ : c ≫ pullback.fst q₀ e₀ = i₀ := pullback.lift_fst _ _ _
  have c₂ : c ≫ pullback.snd q₀ e₀ = t₀ := pullback.lift_snd _ _ _
  have hp : IsPullback (τ ≫ c) t (pullback.snd q₀ e₀) f := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, c₂, hτ.w]) (IsPullback.of_hasPullback q₀ e₀)
    rw [Category.assoc, c₁, hi, he]
    exact H.paste_horiz hγ
  have hc : IsPullback τ (𝟙 T) c (τ ≫ c) := by
    refine IsPullback.of_bot ?_ (by simp) hp
    rw [c₂, Category.id_comp]
    exact hτ
  haveI : IsIso c := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{0})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hc.flip
    (fpqc_of_isPullback hp) (inferInstanceAs (IsIso (𝟙 T)))
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) c₁ c₂

end GlobalTheory.ExtDescent

namespace GlobalTheory

open ExtDescent

theorem splitTorus_extension_descends :
    ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [GrpObj B₀] (X : Type) [AddCommGroup X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap β) φG → IsGrpPullback B B₀ (spMap β) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) (q₀ : G₀ ⟶ B₀) (i₀ : splitTorus (Sp k) X ⟶ G₀), φG ≫ q₀.left = q.left ≫ φ → GlobalTheory.SplitTorus.bcMap (spMap β) X ≫ i₀.left = i.left ≫ φG → IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → IsMonHom q₀ ∧ Flat q₀.left ∧ Surjective q₀.left ∧ QuasiCompact q₀.left ∧ IsMonHom i₀ ∧ IsPullback i₀ (toUnit _) q₀ (η[B₀] : 𝟙_ _ ⟶ B₀) := by
  intro k K _ _ β G B _ _ G₀ B₀ _ _ X _ φG φ hG hB q i q₀ i₀ wq wi hq hfl hsu hqc hi H
  haveI h₁ : Flat (spMap β) := inferInstance
  haveI h₂ : Surjective (spMap β) := inferInstance
  haveI h₃ : QuasiCompact (spMap β) := inferInstance
  have hγ : IsPullback φG q.left q₀.left φ := by
    refine IsPullback.of_bot ?_ wq hB.1
    rw [Over.w, Over.w]
    exact hG.1
  have hφ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) φ :=
    fpqc_of_isPullback hB.1
  haveI := flat_descendsAlong_fpqc
  haveI := quasiCompact_descendsAlong_fpqc.{0}
  have hT := SplitTorus.isGrpPullback_bcMap (spMap β) X
  refine ⟨isMonHom_of_grpPullback hG hB q q₀ wq,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) hγ.flip hφ hfl,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective) hγ.flip hφ hsu,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @QuasiCompact) hγ.flip hφ hqc,
    isMonHom_of_grpPullback hT hG i i₀ wi, ?_⟩
  have H' : IsPullback i.left (splitTorus (Sp K) X).hom q.left (η[B]).left :=
    H.map (Over.forget _)
  have H₀ := isPullback_of_baseChange H' hT.1 hγ wi (unit_comm hB)
  exact IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext H₀.w) H₀

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxEvEqMapArc
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

theorem hasSum_zpow_of_form_le {O C X : Type} [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (φ : PowerSeries O →+* C) (h1 : ∀ f, ‖φ f‖ ≤ 1) (hX : ‖φ PowerSeries.X‖ < 1) (u : Cˣ)
    (hu : (u : C) = φ PowerSeries.X) (B : LinearMap.BilinForm ℤ X) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (y : X) {m : ℕ} (hm : m ≠ 0) {D : ℤ} (hD : 0 < D) (E : X → ℤ)
    (hE : ∀ χ, B (y + m • χ) (y + m • χ) ≤ D * E χ) (a : X → O) :
    HasSum (fun χ => ((u ^ E χ : Cˣ) : C) * φ (PowerSeries.C (a χ)))
      (φ (PowerSeries.mk fun n => ∑ᶠ (χ : X) (_ : E χ = n), a χ)) := by
  classical
  have hB0 : ∀ x, 0 ≤ B x x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hp x hx).le
  have hE0 : ∀ χ, 0 ≤ E χ := by
    intro χ
    have h := hE χ
    have h' := hB0 (y + m • χ)
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hinj : Function.Injective (fun χ : X => y + m • χ) := by
    intro a b h
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa using h
    exact smul_right_injective X (Int.natCast_ne_zero.mpr hm) h'
  have hQ := GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef hs hp
  have hfin : ∀ n : ℕ, {χ | (E χ).toNat = n}.Finite := by
    intro n
    refine (Set.Finite.preimage (fun _ _ _ _ h => hinj h)
      (GlobalTheory.ClassMin.finite_sublevel hQ ((D * n : ℤ) : ℝ))).subset ?_
    intro χ hχ
    simp only [Set.mem_setOf_eq] at hχ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.ClassMin.ofIntBilin_apply]
    have h := hE χ
    have h0 := hE0 χ
    have h2 := hB0 (y + m • χ)
    have hEn : E χ = n := by omega
    rw [hEn] at h
    have h3 : (B (y + m • χ) (y + m • χ) : ℝ) ≤ ((D * n : ℤ) : ℝ) := by exact_mod_cast h
    have h4 : (0 : ℝ) ≤ B (y + m • χ) (y + m • χ) := by exact_mod_cast h2
    linarith
  have h := GlobalTheory.hasSum_map_powerSeries_mk_finsum O C X φ h1 hX (fun χ => (E χ).toNat) hfin a
  have hf : (fun χ => ((u ^ E χ : Cˣ) : C) * φ (PowerSeries.C (a χ))) =
      fun χ => φ (PowerSeries.C (a χ)) * φ PowerSeries.X ^ (E χ).toNat := by
    funext χ
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (hE0 χ)
    rw [hk]
    simp [hu, mul_comm]
  have hg : (fun n : ℕ => ∑ᶠ (χ : X) (_ : E χ = n), a χ) =
      fun n : ℕ => ∑ᶠ (χ : X) (_ : (E χ).toNat = n), a χ := by
    funext n
    refine finsum_congr fun χ => ?_
    have h0 := hE0 χ
    have hiff : (E χ = n) = ((E χ).toNat = n) := propext (by omega)
    rw [hiff]
  rw [hf, hg]
  exact h

theorem form_le_exponent {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k)
    {j : ℕ} (hj : j ∣ k) (hj0 : j ≠ 0) (x z : N.X) (s : ℤ) (hs : (m : ℤ) ^ 2 * β.be z z ≤ s) :
    β.be x x ≤ 4 * (m : ℤ) ^ 2 * (β.be x x / (2 * m ^ 2) + β.be z x / j + s) := by
  have hB0 : ∀ y, 0 ≤ β.be y y := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (β.pos y hy).le
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have hk : k = 0 := by simpa using hm
    have h0 : β.be x x = 0 := by
      have h := β.dvd x x
      simpa [hk] using h
    simp [h0]
  · have hmk : (2 * (m : ℤ) ^ 2) ∣ 2 * (k : ℤ) := mul_dvd_mul_left 2 (by exact_mod_cast hm)
    have hjk : (j : ℤ) ∣ 2 * (k : ℤ) := dvd_mul_of_dvd_right (by exact_mod_cast hj) 2
    obtain ⟨q, hq⟩ := dvd_trans hmk (β.dvd x x)
    obtain ⟨c, hc⟩ := dvd_trans hjk (β.dvd z x)
    have hm2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
    have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
    have hq' : β.be x x / (2 * m ^ 2) = q := by
      rw [hq]
      exact Int.mul_ediv_cancel_left q hm2.ne'
    have hc' : β.be z x / j = c := by
      rw [hc]
      exact Int.mul_ediv_cancel_left c (by omega)
    rw [hq', hc']
    have hexp := hB0 ((j : ℤ) • x + (2 * (m : ℤ) ^ 2) • z)
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hexp
    rw [β.symm x z, hc] at hexp
    have ha := hB0 z
    have hs0 : 0 ≤ s := le_trans (mul_nonneg (by positivity) ha) hs
    have hjj : (0 : ℤ) ≤ (j : ℤ) ^ 2 - 1 := by nlinarith
    have h5 : 0 ≤ 4 * (m : ℤ) ^ 2 * (((j : ℤ) ^ 2 - 1) * s + (s - (m : ℤ) ^ 2 * β.be z z)) :=
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg hjj hs0) (by linarith))
    have key : 0 ≤ (j : ℤ) ^ 2 * (β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s) := by
      nlinarith [hexp, h5]
    have hX : 0 ≤ β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_pos_of_neg (by positivity : (0 : ℤ) < (j : ℤ) ^ 2) hneg
      linarith
    nlinarith [hX, hq]

theorem twist_tx_ev_eq_map_arc : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (u : Cˣ), (u : C) = φ PowerSeries.X → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (β₀ : N₀.Form k) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = β₀.be y z) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p₀ : N₀.QT (m ^ 2)) (p : N.QT (m ^ 2)), p.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p.1.2 → (N.twist β u).tx m (N.twQ β u hm p) = I.lam * φ (N₀.arcTx β₀.be m p₀) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q₀ : N₀.QT j) (q : N.QT j), j ≠ 0 → q.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q.1.2 → ∀ s : ℕ, (m : ℤ) ^ 2 * β₀.be q₀.1.1.toAdd q₀.1.1.toAdd ≤ s → (u : C) ^ s * (N.twist β u).ev m (N.twQ β u hm p) (N.twQ β u hj q).1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv β₀.be m p₀ q₀ s) := by
  intro O C _ _ _ _ φ h1 hX u hu N₀ N I k β₀ β hβ m hm hmo p₀ p hp1 hp2
  have hm0 : m ≠ 0 := hmo.pos.ne'
  have hT := (_root_.GlobalTheory.Ex.NumD.hom_transport O C (φ.comp PowerSeries.C) N₀ N I).2.2.2.2 m hmo p₀ p hp1 hp2
  have hpt : ∀ χ₀ : N₀.X, p.1.1.toAdd + m • I.e χ₀ = I.e (p₀.1.1.toAdd + m • χ₀) := by
    intro χ₀
    rw [hp1, map_add (f := _), map_nsmul]
  have hdiv2 : ∀ x y, (2 * (m : ℤ) ^ 2) ∣ β₀.be x y := fun x y =>
    dvd_trans (mul_dvd_mul_left 2 (by exact_mod_cast hm)) (β₀.dvd x y)
  have hD2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
  constructor
  · have hsum := hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0 hD2
      (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2))
      (fun χ => (Int.mul_ediv_cancel' (hdiv2 _ _)).ge) (fun χ => N₀.txT m p₀ χ)
    have key : ∀ χ₀, (N.twist β u).txT m (N.twQ β u hm p) (I.e χ₀) =
        (I.lam : C) * (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2)) :
          Cˣ) : C) * φ (PowerSeries.C (N₀.txT m p₀ χ₀))) := by
      intro χ₀
      rw [(_root_.GlobalTheory.Ex.twist_terms C N k β u m hm hmo p (I.e χ₀)).1, hpt, hβ, (hT χ₀).1, RingHom.comp_apply]
      ring
    show ∑' χ, (N.twist β u).txT m (N.twQ β u hm p) χ = _
    refine HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)
    exact (congrArg (fun f => HasSum f ((I.lam : C) * φ (N₀.arcTx β₀.be m p₀))) (funext key)).mpr
      (hsum.mul_left (I.lam : C))
  · intro j hj q₀ q hj0 hq1 hq2 s hs
    have hsum := hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0
      (D := 4 * (m : ℤ) ^ 2) (by positivity)
      (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2) +
        β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ) / j + s)
      (fun χ => form_le_exponent β₀ hm hj hj0 _ _ (s : ℤ) hs) (fun χ => N₀.evT m p₀ q₀.1.2 χ)
    have key : ∀ χ₀, (u : C) ^ s * (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 (I.e χ₀) =
        ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) *
          (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2) +
            β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ₀) / j + s) : Cˣ) : C) *
            φ (PowerSeries.C (N₀.evT m p₀ q₀.1.2 χ₀))) := by
      intro χ₀
      rw [(_root_.GlobalTheory.Ex.twist_terms C N k β u m hm hmo p (I.e χ₀)).2.1 j hj q hj0, hpt, hq1, hβ, hβ,
        (hT χ₀).2 q₀.1.2 q.1.2 hq2, RingHom.comp_apply]
      simp only [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    show (u : C) ^ s * ∑' χ, (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = _
    rw [← tsum_mul_left]
    refine HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)
    exact (congrArg (fun f => HasSum f (((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) *
      φ (N₀.arcEv β₀.be m p₀ q₀ s))) (funext key)).mpr
      (hsum.mul_left ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C))

end GlobalTheory.Ex
end

