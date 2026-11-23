module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentLeDim
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaFamilyOverOpenClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0205
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversalReducedBases
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem range_subset_iff_of_charts {X Hk S S₁ S₂ U G₀ G G₁ G₂ P : Scheme.{0}} {g₀ : G₀ ⟶ Hk} {gU : U ⟶ X}
    {m₁ : G₀ ⟶ U} {f : S ⟶ X} {g : G ⟶ S} {mu : G ⟶ U} (hmu : IsPullback mu g gU f)
    {K : Set G₀} {K' : Set G}
    {q₁ : S₁ ⟶ S} {g₁ : G₁ ⟶ S₁} {a₁ : G₁ ⟶ G} (ha₁ : a₁ ≫ g = g₁ ≫ q₁) {h₁ : S₁ ⟶ Hk} {n₁ : G₁ ⟶ G₀}
    (hn₁ : IsPullback n₁ g₁ g₀ h₁) (e₁ : n₁ ≫ m₁ = a₁ ≫ mu) (k₁ : a₁ ⁻¹' K' = n₁ ⁻¹' K)
    {q₂ : S₂ ⟶ S} {g₂ : G₂ ⟶ S₂} {a₂ : G₂ ⟶ G} (ha₂ : a₂ ≫ g = g₂ ≫ q₂) {h₂ : S₂ ⟶ Hk} {n₂ : G₂ ⟶ G₀}
    (hn₂ : IsPullback n₂ g₂ g₀ h₂) (e₂ : n₂ ≫ m₁ = a₂ ≫ mu) (k₂ : a₂ ⁻¹' K' = n₂ ⁻¹' K)
    (x₁ : P ⟶ S₁) (x₂ : P ⟶ S₂) (hx : x₁ ≫ q₁ = x₂ ≫ q₂)
    (u₁ u₂ : P ⟶ G₀) (hu₁ : u₁ ≫ g₀ = x₁ ≫ h₁) (hu₂ : u₂ ≫ g₀ = x₂ ≫ h₂) (hu : u₁ ≫ m₁ = u₂ ≫ m₁) :
    (Set.range u₁ ⊆ K ↔ Set.range u₂ ⊆ K) := by
  have key : ∀ {A B : Scheme.{0}} (w : P ⟶ A) (c : A ⟶ B) (L : Set B),
      Set.range (w ≫ c) ⊆ L ↔ Set.range w ⊆ c ⁻¹' L := by
    intro A B w c L
    simp [Set.range_subset_iff]
  obtain ⟨w₁, hw₁, hw₁'⟩ := hn₁.exists_lift u₁ x₁ hu₁
  obtain ⟨w₂, hw₂, hw₂'⟩ := hn₂.exists_lift u₂ x₂ hu₂
  have hw : w₁ ≫ a₁ = w₂ ≫ a₂ := by
    apply hmu.hom_ext
    · rw [Category.assoc, Category.assoc, ← e₁, ← e₂, ← Category.assoc, ← Category.assoc, hw₁, hw₂, hu]
    · rw [Category.assoc, Category.assoc, ha₁, ha₂, ← Category.assoc, ← Category.assoc, hw₁', hw₂', hx]
  rw [← hw₁, ← hw₂, key, key, ← k₁, ← k₂, ← key, ← key, hw]

theorem exists_kerScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ Z : KerScheme Xo 𝔓 p i, EtSet Z.o₁.t.G Z.K := by
  intro E _ _ _ H D l Xo 𝔓 p i hA
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨Hk, π₁, o₁, m₁, K, fin₁, et₁, hK, hE, hpt, hex⟩ := _root_.GlobalTheory.HkFam.exists_heckeKernelScheme E H D l Xo 𝔓 p i hA
  refine ⟨⟨Hk, π₁, fin₁, et₁, o₁, m₁, K, hK, hE, ?_⟩, hE⟩
  intro S s hS o K' hE' hK'
  obtain ⟨f, ⟨hf, ⟨mu⟩⟩, hfu⟩ := Xo.rep S s hS o
  obtain ⟨S', π, o', m, τ, hπ₁, hπ₂, hπ₃, hL⟩ := _root_.GlobalTheory.exists_cover_lists_heckeSet E H D l 𝔓 p i S s o K' hA hE' hK'
  have hK'' := ((GlobalTheory.heckeSets_pull E H D 𝔓 p i S S' o.t o'.t π m.toSABMap o.proper).2 K').1 hK'
  obtain ⟨mu', hmu'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 f π mu).1 m
  obtain ⟨h', n', hh', hn', hKn'⟩ := hex S' (π ≫ s) o' (π ≫ f) mu' τ _ hL hK''
  have cm := m.cart.1
  have cm₁ := m₁.cart.1
  have cn' := n'.cart.1
  haveI : IsReduced S' := GlobalTheory.isReduced_of_smooth_of_isReduced π
  haveI : IsReduced (pullback π π : Scheme.{0}) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst π π)
  have hd : pullback.fst π π ≫ h' = pullback.snd π π ≫ h' := by
    have h0 : (pullback.fst π π ≫ h') ≫ π₁ = (pullback.snd π π ≫ h') ≫ π₁ := by
      rw [Category.assoc, Category.assoc, hh', pullback.condition_assoc]
    refine hom_ext_of_geometric_points _ _ _ π₁ _ _ h0 ?_
    intro k _ _ x
    refine hpt k _ _ (by rw [Category.assoc, Category.assoc x, h0]) ?_
    intro u u' huu
    exact range_subset_iff_of_charts mu.cart.1 cm.w cn' (hn'.trans hmu') hKn' cm.w cn' (hn'.trans hmu') hKn'
      (x ≫ pullback.fst π π) (x ≫ pullback.snd π π) (by rw [Category.assoc, Category.assoc, pullback.condition])
      u.left u'.left (by rw [Category.assoc]; exact Over.w u) (by rw [Category.assoc]; exact Over.w u') huu
  obtain ⟨h, hh⟩ : ∃ h : S ⟶ Hk, π ≫ h = h' := by
    suffices hc : ∀ {Z : Scheme.{0}} (a b : Z ⟶ S'), a ≫ π = b ≫ π → a ≫ h' = b ≫ h' from
      ⟨EffectiveEpi.desc π h' hc, EffectiveEpi.fac π h' hc⟩
    focus
      intro Z a b hab
      have := congrArg (pullback.lift a b hab ≫ ·) hd
      simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  have hhf : h ≫ π₁ = f := by
    rw [← cancel_epi π, ← Category.assoc, hh, hh']
  subst hhf
  obtain ⟨n, hn⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ h m₁).2 mu
  have cn := n.cart.1
  have hmn : m.toSABMap.φ ≫ n.toSABMap.φ = n'.toSABMap.φ := by
    apply cm₁.hom_ext
    · rw [Category.assoc, ← hn]
      exact (hn'.trans hmu').symm
    · rw [Category.assoc, cn.w, cn'.w, ← Category.assoc, cm.w, Category.assoc, hh]
  have hsurj : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback cm.flip hπ₃
  have hKn : K' = n.toSABMap.φ ⁻¹' K := by
    apply hsurj.surj.preimage_injective
    rw [hKn', ← hmn]
    ext y
    simp
  refine ⟨h, ⟨by rw [← Category.assoc, hf], n, hKn⟩, ?_⟩
  rintro h₂ ⟨hs₂, n₂, hKn₂⟩
  obtain ⟨mu₂, hmu₂⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ h₂ m₁).1 n₂
  have h0 : h₂ ≫ π₁ = h ≫ π₁ := hfu _ ⟨by rw [Category.assoc, hs₂], ⟨mu₂⟩⟩
  have hrig : ∀ (f₂ : S ⟶ Xo.X) (mu₂ : ObjMap o Xo.univ f₂), f₂ = h ≫ π₁ → mu₂.toSABMap.φ = mu.toSABMap.φ := by
    intro f₂ mu₂ e
    subst e
    exact GlobalTheory.obj_rigid_closed laws E H D l _ _ _ _ _ _ _ _ Xo.univ o _ (Or.inl hS) _ _
      fun a => ⟨_, mu₂.eta a, mu.eta a⟩
  have e₂ := hmu₂.symm.trans (hrig _ mu₂ h0)
  refine hom_ext_of_geometric_points _ _ _ π₁ _ _ h0 ?_
  intro k _ _ x
  refine hpt k _ _ (by rw [Category.assoc, Category.assoc x, h0]) ?_
  intro u u' huu
  exact range_subset_iff_of_charts (q₁ := 𝟙 S) (q₂ := 𝟙 S) (a₁ := 𝟙 _) (a₂ := 𝟙 _) (K' := K') mu.cart.1 (by simp) n₂.cart.1
    (by rw [Category.id_comp]; exact e₂) (by rw [← hKn₂]; simp) (by simp) cn (by rw [Category.id_comp]; exact hn.symm)
    (by rw [← hKn]; simp) x x rfl u.left u'.left (Over.w u) (Over.w u') huu

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliPrimePowerFullLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FullLevel

theorem finiteDimensional_KA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    FiniteDimensional ℚ (KA l) := by
  have hA := l.A_pos
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  rcases hx with rfl | hx
  · have h2 : H.rt0 ^ 2 = algebraMap ℚ ℂ (-(H.d : ℚ)) := by
      rw [H.sqrt_neg_disc_sq]; simp
    have hi : IsIntegral ℚ (H.rt0 ^ 2) := by rw [h2]; exact isIntegral_algebraMap
    exact IsIntegral.of_pow two_pos hi
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have hz : IsPrimitiveRoot (zeta l.A) l.A := by
      unfold zeta; exact Complex.isPrimitiveRoot_exp l.A hA.ne'
    refine IsIntegral.of_pow hA ?_
    rw [hz.pow_eq_one]; exact isIntegral_one

private theorem constPt_comp' {k : Type} [Field k] {X Y : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X)
    (f : X ⟶ Y) : constPt (x ≫ f) = constPt x ≫ f := by
  simp only [constPt, Category.assoc]

theorem moduli_of_family (hL : Out.Laws) (hL2 : Out.Laws2)
    (hth : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {g : ℕ} {J : Type} (a : J → 𝓞 E)
    (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (hbas : IsSympBasis D bas) (hw : a w = H.w0)
    (hw' : a w' = H.bar H.w0) (hgen : Subring.closure (Set.range a) = ⊤) (l : Level H) (hMA : l.M ∣ l.A)
    {o : Type} [CommRing o] [IsDomain o] [Algebra o (KA l)] [hfr : IsFractionRing o (KA l)] (b : TBase o l.A) (ρ : o)
    (hρ : algebraMap o (KA l) ρ = (baseKA l).ρ) (hζ : algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ)
    {U : Scheme.{0}} (sU : U ⟶ Sp o) (tU : TObj g l.A J b sU) (τU : SAB H U) (hq : IsQProjOver sU)
    (hτ : IsPEL D a bas ρ tU τU)
    (hdim : ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ U), IsOpenImmersion x →
      x ≫ sU = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R),
        (D.dim : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q))
    (hinj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ U) (s' : Sp R ⟶ Sp o) (t : TObj g l.A J b s'),
      x ≫ sU = y ≫ sU → TMap t tU x → TMap t tU y → x = y)
    (hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g l.A J b s') (τ : SAB H S), IsReduced S →
      IsPEL D a bas ρ t τ → (∀ (K : Type) [Field K], (Sp K ⟶ S) → CharZero K) →
      ∃! f : S ⟶ U, f ≫ sU = s' ∧ TMap t tU f) :
    Nonempty (Moduli D l) := by
  classical
  obtain ⟨X, p, sX, sq⟩ : ∃ (X : Scheme.{0}) (p : X ⟶ U) (sX : X ⟶ Sp (KA l)),
      IsPullback p sX sU (spMap (algebraMap o (KA l))) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have hqX : IsQProjOver sX := isQProjOver_of_isPullback_spMap _ sq hq
  have hlft : LocallyOfFiniteType sX := lft_of_qproj hqX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : FiniteDimensional ℚ (KA l) := finiteDimensional_KA l
  haveI : Algebra.IsAlgebraic ℚ (KA l) := Algebra.IsAlgebraic.of_finite ℚ (KA l)
  obtain ⟨tX, htX⟩ := tObj_pull o g l.A J b U X sU (sX ≫ spMap (algebraMap o (KA l))) p tU sq.w
  obtain ⟨τX, hτX⟩ := exists_isPEL_of_tmap E H D g J a bas l.A o b ρ U X sU
    (sX ≫ spMap (algebraMap o (KA l))) tU tX τU p sq.w htX hτ
  obtain ⟨ob, hob⟩ := ThetaToObj.exists_obj_under hL hL2 E H D g J a bas l o b ρ X sX tX τX hMA hbas hfr hρ hζ
    (Or.inr inferInstance) hτX
  have hsep : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x1 x2 : Sp R ⟶ X) (s' : Sp R ⟶ Sp o)
      (t' : TObj g l.A J b s'), TMap t' tX x1 → TMap t' tX x2 → x1 ≫ sX = x2 ≫ sX → x1 = x2 := by
    intro R _ _ x1 x2 s' t' h1 h2 hs
    refine sq.hom_ext ?_ hs
    refine hinj R _ _ s' t' ?_ (TMap.comp h1 htX) (TMap.comp h2 htX)
    rw [Category.assoc, Category.assoc, sq.w, ← Category.assoc, hs, Category.assoc]
  refine ⟨{ X := X, s := sX, qproj := hqX, smooth := ?_, univ := ob, rep := ?_, unram := ?_ }⟩
  · refine smoothOfRelativeDimension_of_dim_of_directions_le (KA l) X sX D.dim hlft ?_ ?_
    · intro R _ _ x hx _ q hq'
      haveI : IsOpenImmersion (x ≫ sq.isoPullback.hom) := inferInstance
      exact dim_generic_chart sU _ hdim R (x ≫ sq.isoPullback.hom) q hq'
    · intro K' _ _ r β x hxs hdir
      have hρsq : ρ ^ 2 = -(H.d : o) := by
        apply IsFractionRing.injective o (KA l)
        rw [map_pow, hρ, (baseKA l).ρ_sq]; simp
      have hb : x ≫ sX ≫ spMap (algebraMap o (KA l)) =
          spMap ((algebraMap K' (TrivSqZeroExt K' (Fin r → K'))).comp (β.comp (algebraMap o (KA l)))) := by
        rw [← Category.assoc, hxs, ← spMap_comp]
      obtain ⟨t1, ht1⟩ := tObj_pull o g l.A J b X _ (sX ≫ spMap (algebraMap o (KA l))) _ x tX hb
      obtain ⟨τ1, hτ1⟩ := exists_isPEL_of_tmap E H D g J a bas l.A o b ρ X _
        (sX ≫ spMap (algebraMap o (KA l))) _ tX t1 τX x hb ht1 hτX
      haveI : CharZero K' := charZero_of_hom (spMap β)
      refine _root_.GlobalTheory.PelTangent.tangent_le_dim hL hL2 hth E H D g J a w w' bas l.A o b ρ K' r (β.comp (algebraMap o (KA l))) t1 τ1
        hw hw' hρsq hτ1 ?_
      intro lam t' h1 h2
      apply hdir lam
      rw [constPt_comp']
      refine hsep (DualNumber K') _ _ _ t' (TMap.comp h1 ht1) (TMap.comp h2 ht1) ?_
      simpa only [constPt_comp'] using eq_constPt ((spMap (dirMap lam) ≫ x) ≫ sX)
  · intro S s' hS o'
    obtain ⟨t', ht'u, ht'p⟩ := ObjTheta.exists_tObj hL hL2 E H D g J a bas l (KA l) o (baseKA l) b ρ
      (algebraMap o (KA l)) S s' o' hbas hρ hζ
    have hch : ∀ (K : Type) [Field K], (Sp K ⟶ S) → CharZero K := fun K _ y => charZero_of_hom (y ≫ s')
    obtain ⟨f, ⟨hf1, hf2⟩, hfu⟩ := hrep S (s' ≫ spMap (algebraMap o (KA l))) t' o'.t hS ht'p hch
    have hiff := fun (f' : S ⟶ X) => UnderMap.objMap_iff_tMap hL hL2 E H D g J a bas l (KA l) o (baseKA l) b X S
      sX s' (sX ≫ spMap (algebraMap o (KA l))) (s' ≫ spMap (algebraMap o (KA l))) ob o' tX t' f' hMA hgen hob ht'u
    refine ⟨sq.lift f s' hf1, ⟨sq.lift_snd _ _ _, (hiff _).mpr (TMap.cancel htX (by rw [sq.lift_fst]; exact hf2))⟩, ?_⟩
    rintro f2 ⟨hf2s, hm⟩
    have htm : TMap t' tX f2 := (hiff f2).mp hm
    apply sq.hom_ext
    · rw [sq.lift_fst]
      apply hfu
      refine ⟨?_, TMap.comp htm htX⟩
      rw [Category.assoc, sq.w, ← Category.assoc, hf2s]
    · rw [sq.lift_snd, hf2s]
  · intro k _ x o' hm1 hm2
    obtain ⟨t', ht'u, -⟩ := ObjTheta.exists_tObj hL hL2 E H D g J a bas l (KA l) o (baseKA l) b ρ
      (algebraMap o (KA l)) _ (x ≫ sX) o' hbas hρ hζ
    have hiff := fun (f' : Sp (DualNumber k) ⟶ X) => UnderMap.objMap_iff_tMap hL hL2 E H D g J a bas l (KA l) o
      (baseKA l) b X _ sX (x ≫ sX) (sX ≫ spMap (algebraMap o (KA l))) ((x ≫ sX) ≫ spMap (algebraMap o (KA l)))
      ob o' tX t' f' hMA hgen hob ht'u
    refine hsep (DualNumber k) x (constPt x) _ t' ((hiff x).mp hm1) ((hiff _).mp hm2) ?_
    simpa only [constPt_comp'] using eq_constPt (x ≫ sX)

theorem exists_generating_family {E : Type} [Field E] [NumberField E] (u u' : 𝓞 E) :
    ∃ (J : Type) (_ : Finite J) (a : J → 𝓞 E) (w w' : J), a w = u ∧ a w' = u' ∧ Subring.closure (Set.range a) = ⊤ := by
  classical
  let bs := NumberField.RingOfIntegers.basis E
  refine ⟨Option (Option (Module.Free.ChooseBasisIndex ℤ (𝓞 E))), inferInstance,
    fun i => Option.elim i u (fun i' => Option.elim i' u' (fun k => bs k)), none, some none, rfl, rfl, ?_⟩
  rw [eq_top_iff]
  intro x hx0
  clear hx0
  have hx : x ∈ Submodule.span ℤ (Set.range bs) := by rw [bs.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact Subring.subset_closure ⟨some (some k), rfl⟩
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul n y _ hy => exact zsmul_mem hy n

end GlobalTheory.ZM.FullLevel


open GlobalTheory.ZM.FullLevel in
theorem GlobalTheory.ZM.exists_moduli_prime_power_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ j : ℕ, ∀ l : Level H, l.M = n → l.A = (n ^ j) ^ 2 → Nonempty (Moduli D l) := by
  intro hL hL2 hth hU E _ _ _ H D n hpq hn hodd
  obtain ⟨bas, hbas⟩ := ZM.exists_isSympBasis E H D
  obtain ⟨J, hJ, a, w, w', hw, hw', hgen⟩ := exists_generating_family (E := E) H.w0 (H.bar H.w0)
  obtain ⟨Mat, κ, hGood⟩ := T.isGoodThetaComplexClass_unitaryFullLevel hL hL2 hth hU E H D _ J a w w' bas hpq hbas hw hw' hgen
  obtain ⟨j₁, hj₁⟩ := hGood n hn hodd
  obtain ⟨j₂, hj₂⟩ := _root_.GlobalTheory.ZM.OpenFamily.nonempty_wFam hL hL2 _ J Mat κ n w w' hn hodd
  obtain ⟨j₃, hj₃⟩ := _root_.GlobalTheory.ZM.UnivProp.existsUnique_map_of_wFam hL hL2 _ J Mat κ n w w' hn hodd
  refine ⟨max (max j₁ j₂) (max j₃ 1), ?_⟩
  intro l hM hA
  have hj1 : j₁ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_left (le_max_left _ _)
  have hj2 : j₂ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_left (le_max_right _ _)
  have hj3 : j₃ ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_right (le_max_left _ _)
  have hj0 : 1 ≤ max (max j₁ j₂) (max j₃ 1) := le_max_of_le_right (le_max_right _ _)
  generalize max (max j₁ j₂) (max j₃ 1) = j at hj1 hj2 hj3 hj0 hA
  obtain ⟨o, _, b, em, ρ, _, har, hfr, hem, hρ, hζ⟩ := IntegersAway.exists_tBase_fractionRing E H l
  cases l
  dsimp only at hA hM
  subst hA
  have hM' := hM.symm
  subst hM'
  haveI := har.1
  have hemρ : em ρ = H.rt0 := by rw [← hem, hρ]; rfl
  have h3n : 3 ≤ n := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.mpr even_two) hodd
    omega
  have hN3 : 3 ≤ n ^ j := le_trans h3n (Nat.le_self_pow (by omega) n)
  have hoddN : Odd (n ^ j) := hodd.pow
  have hGd := hj₁ j hj1 (n ^ j) rfl o b em ρ hemρ
  obtain ⟨F⟩ := hj₂ j hj2 o b em _ D.dim har hGd
  obtain ⟨hqU, -, hredU, hinjU⟩ := _root_.GlobalTheory.ZM.WFam.qproj_flat_reduced_ext hL hL2 o _ n (n ^ j) J b em _ Mat κ F hoddN
  have hqU' : IsQProjOver (F.U.ι ≫ F.Y.s) := hqU.resolve_right (not_not.mpr inferInstance)
  haveI := hredU
  haveI := lft_of_qproj hqU'
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨τU, hτU⟩ := T.exists_isPELTriple_of_dense_fibres hL hL2 hth E H D _ J a bas w w' hpq hbas hw hw' hgen _ o b em ρ F.U.toScheme
    (F.U.ι ≫ F.Y.s) F.univ hemρ har.2.2 F.dense
  refine moduli_of_family hL hL2 hth D a w w' bas hbas hw hw' hgen _
    (dvd_pow (dvd_pow_self n (by omega)) two_ne_zero) b ρ hρ hζ (F.U.ι ≫ F.Y.s) F.univ τU hqU' hτU
    (_root_.GlobalTheory.ZM.GenericDim.le_ringKrullDim_genericFibre hL hL2 _ n (n ^ j) J Mat κ w w' o b em _ D.dim F hN3 hoddN har hGd) hinjU ?_
  intro S s' t τ hS hP hch
  refine hj₃ j hj3 o b em _ D.dim har hGd F S s' t hS ?_ ?_
  · refine Dense.mono ?_ dense_univ
    intro p _
    haveI := hch _ (S.fromSpecResidueField p)
    exact ⟨_, inferInstance, S.fromSpecResidueField p,
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply p _⟩,
      T.pelObject_fibre_from_complex_charZero hL hL2 E H D _ J a w w' bas hpq hbas hw hw' hgen (n ^ j) o b em ρ hemρ har S s' t τ hP _ _⟩
  · intro K _ _ x t' hT
    haveI := hch K x
    obtain ⟨K₀, _, β, i, e, t₀, tx, tc, -, -, htx, htx0, htc0, hC⟩ :=
      T.pelObject_fibre_from_complex_charZero hL hL2 E H D _ J a w w' bas hpq hbas hw hw' hgen (n ^ j) o b em ρ hemρ har S s' t τ hP K x
    have s1 := (hGd.shape tc hC).1
    have s2 := ((shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ t₀ tc htc0).2.2 K₀ rfl
      inferInstance inferInstance).1 s1
    have s3 := (shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ t₀ tx htx0).1 s2
    have htt : TMap t' tx (𝟙 _) := TMap.cancel htx (by rw [Category.id_comp]; exact hT)
    exact (shape_prim_pull_and_descend o _ _ J b Mat κ w w' _ _ _ _ _ tx t' htt).1 s3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyPelSmoothGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem ThetaFam.unram_of_mono {o : Type} [CommRing o] {g n N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} (F : ThetaFam n em C) {S : Scheme.{0}} (x : S ⟶ F.MM) [Mono x]
    {s : S ⟶ Sp o} (hs : x ≫ F.s = s) (t : TObj g (N' ^ 2) J b s) (ht : TMap t F.univ x) (K : Type) [Field K]
    (y : Sp (DualNumber K) ⟶ S) (t' : TObj g (N' ^ 2) J b (y ≫ s)) (hy : y ≫ s = constPt y ≫ s)
    (h₁ : TMap t' t y) (h₂ : TMap t' t (constPt y)) : y = constPt y := by
  subst hs
  have hc : constPt (y ≫ x) = constPt y ≫ x := by simp [constPt]
  rw [← cancel_mono x, ← hc]
  have key : ∀ (s' : Sp (DualNumber K) ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s'), s' = (y ≫ x) ≫ F.s →
      TMap t' F.univ (y ≫ x) → TMap t' F.univ (constPt (y ≫ x)) → y ≫ x = constPt (y ≫ x) := by
    rintro _ t' rfl h h'
    exact F.unram K (y ≫ x) t' (by rw [hc, Category.assoc, Category.assoc, hy]) h h'
  refine key _ t' (Category.assoc _ _ _).symm ?_ ?_
  · exact ((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t t').2 x y ht).1 h₁
  · rw [hc]
    exact ((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t t').2 x (constPt y) ht).1 h₂

theorem exists_thetaFam_isPEL_smooth : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∃ (F : ThetaFam n em (PELClass (b := b) D a bas ρ em)) (τ : SAB H F.MM), IsPEL D a bas ρ F.univ τ ∧ SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  intro h1 h2 hcrit hgen hU E _ _ _ H D g J _ a w w' bas hD hbas hw hw' ha n hn hodd
  obtain ⟨Mat, κ, hcl⟩ := GlobalTheory.T.isGoodThetaComplexClass_unitaryFullLevel h1 h2 hgen hU E H D g J a w w' bas hD hbas hw hw' ha
  obtain ⟨j₁, hj₁⟩ := hcl n hn hodd
  obtain ⟨j₂, hj₂⟩ := _root_.GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam h1 h2 hcrit g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em ρ hρ hb => ?_⟩
  have hgood := hj₁ j (le_of_max_le_left hj) _ rfl o b em ρ hρ
  obtain ⟨F⟩ := hj₂ j (le_of_max_le_right hj) o b em _ _ hb hgood
  obtain ⟨τ, hτ⟩ := GlobalTheory.thetaFam_isPEL h1 h2 hgen E H D g J a w w' bas hD hbas hw hw' ha n _ o b em ρ hρ hb F
  refine ⟨F, τ, hτ, ThetaFam.smooth_genericFibre h1 h2 g n _ J Mat κ w w' o b em _ _ F hb hgood ?_⟩
  intro R _ _ _ _ _ x hx hs hem
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull o g _ J b _ _ F.s _ x F.univ hs
  obtain ⟨τ', hτ'⟩ := GlobalTheory.PELPull.isPEL_pull E H D g _ J a bas o b ρ _ _ F.s _ x F.univ t τ hs ht hτ
  have hρ2 : ρ ^ 2 = -(H.d : o) := hb.2.2 (by rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast])
  have hft : Algebra.FiniteType o R := by
    have := ((GlobalTheory.isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB F.s).1 F.qproj).1
    have h : LocallyOfFiniteType (spMap (algebraMap o R)) := hs ▸ inferInstance
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h)
  exact _root_.GlobalTheory.PelTan.finrank_derivation_le h1 h2 hgen hU E H D g J a w w' bas hD hbas hw hw' ha _ o b ρ R t τ' hρ2 hτ' hft
    (fun y t' hy h₁ h₂ => F.unram_of_mono x hs t ht ℂ y t' hy h₁ h₂)

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionHomImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsRepMap

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorsionFormCompare GlobalTheory.TorusModel GlobalTheory.FieldRestrictionTest

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

variable {Gt : Over (Sp R)} [GrpObj Gt] {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

end Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

end GlobalTheory.TorsRepMap
end
end

