module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairData

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeOneObstructionClass
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem exists_isOb1 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsFun → L'.IsFun → L.IsLift L' n l → ∀ w : Glob1 F, ∃ c, L.IsOb1 L' n l α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l hL hL' hl w
  classical
  have hdiff : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)),
      (L'.ρ a).comp (l T) b - (l T').comp (L.ρ (n.G.map a)) b ∈ I.map (algebraMap R (L'.B T')) := by
    intro T T' a b
    rw [← L'.ker, map_sub, sub_eq_zero]
    simp only [AlgHom.comp_apply, L'.nat]
    rw [hl, hl, L.nat]
    exact (n.naturality a _).symm
  have hκ : ∀ (T T' : C') (a : T ⟶ T'), ∃ κ : Ω[F.obj (n.G.obj T)⁄R₀] →+ L'.B T',
      IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) κ := fun T T' a ↦
    ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L'.B T') I hI π hπ (L.p _) (L.semi _)
      (L.surj _) (L.ker _) _).1 _ (hdiff T T' a)).exists
  choose κ hκ using hκ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) σ := fun T ↦
    _root_.GlobalTheory.Obs.exists_isSig R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' : C') (a : T ⟶ T'), ∃ y : R₁ ⊗[R₀] F'.obj T', α.KerQ y ∧ σ T' y = κ T T' a (w.1 _) :=
    fun T T' a ↦ (_root_.GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T')
      (L'.surj T') (L'.ker T') (σ T') (hσ T')).2.2.2 _ ((hκ T T' a).mem _)
  choose z hzq hzs using hz

  have hcomp : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (x : Ω[F.obj (n.G.obj T)⁄R₀]),
      κ T T'' (a ≫ b) x = L'.ρ b (κ T T' a x) + κ T' T'' b (p1 F (n.G.map a) x) := by
    intro T T' T'' a b x
    have t1 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _)
      (L'.B T') (L'.B T'') _ _ _ (hκ T T' a)).1 (L'.ρ b)
    have t2 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk (L.B (n.G.obj T')) (F.obj (n.G.obj T')) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _)
      (L'.B T'') (L'.B T'') _ _ _ (hκ T' T'' b)).2 (L.ρ (n.G.map a)) (mp F (n.G.map a)) (fun y ↦ L.nat _ y)
    have e0 : ((L'.ρ b).comp (l T')).comp (L.ρ (n.G.map a)) = (L'.ρ b).comp ((l T').comp (L.ρ (n.G.map a))) :=
      AlgHom.ext fun _ ↦ rfl
    rw [e0] at t2
    have t3 := ((_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L'.B T'') _ _ _ _ _ t1).2.1 t2)
    have e1 : (L'.ρ b).comp ((L'.ρ a).comp (l T)) = (L'.ρ (a ≫ b)).comp (l T) :=
      AlgHom.ext fun y ↦ (hL' a b _).symm
    have e2 : ((l T'').comp (L.ρ (n.G.map b))).comp (L.ρ (n.G.map a)) = (l T'').comp (L.ρ (n.G.map (a ≫ b))) :=
      AlgHom.ext fun y ↦ by
        show l T'' (L.ρ (n.G.map b) (L.ρ (n.G.map a) y)) = l T'' (L.ρ (n.G.map (a ≫ b)) y)
        rw [Functor.map_comp, hL]
    rw [e1, e2] at t3
    have e3 := (_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L'.B T'') _ _ ((l T'').comp (L.ρ (n.G.map (a ≫ b)))) _ _ (hκ T T'' (a ≫ b))).2.2.1 t3
    exact congrArg (fun f ↦ f x) e3
  let zc : Z1 (ext R₁ F') := ⟨fun T T' a ↦ z T T' a, fun T T' T'' a b ↦ by
    have sn := _root_.GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T') (L'.surj T')
      (L'.ker T') (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'') (L'.ker T'') (L'.ρ b) (mp F' b)
      (fun y ↦ L'.nat b y) (σ T') (σ T'') (hσ T') (hσ T'')
    change z T T'' (a ≫ b) = extHom R₁ (mp F' b) (z T T' a) + z T' T'' b
    rw [← sub_eq_zero]
    haveI := L'.smooth T''
    refine _root_.GlobalTheory.Obs.sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'')
      (L'.ker T'') (σ T'') (hσ T'') _ ?_ ?_
    · have h1 := hzq T T'' (a ≫ b)
      have h2 := sn.2 _ (hzq T T' a)
      have h3 := hzq T' T'' b
      unfold Aug.KerQ at h1 h2 h3 ⊢
      rw [map_sub, map_add (f := _), h1, h2, h3]; simp
    · rw [map_sub, map_add (f := _), ← sn.1, hzs, hzs, hzs, hcomp, w.2 (n.G.map a)]
      simp⟩
  exact ⟨H1.mk _ zc, κ, σ, zc, hκ, hσ, rfl, fun T T' a ↦ ⟨hzq T T' a, hzs T T' a⟩⟩

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeTwoObstructionClass
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isOb2 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F), ∃ c, L.IsOb2 α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w
  have hθ : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ θ : Ω[F.obj T⁄R₀] →+ L.B T'',
      IsTheta I (L.p T) ((L.ρ b).comp (L.ρ a)) (L.ρ (a ≫ b)) θ := by
    intro T T' T'' a b
    obtain ⟨θ, hθ, -⟩ := (theta_classify R R₀ (L.B T) (F.obj T) (L.B T'') I hI π hπ (L.p T) (L.semi T)
      (L.surj T) (L.ker T) ((L.ρ b).comp (L.ρ a))).1 (L.ρ (a ≫ b)) (fun x ↦ by
        rw [← L.ker T'', map_sub, AlgHom.comp_apply, L.nat, L.nat, L.nat, mp_comp, sub_self])
    exact ⟨θ, hθ⟩
  choose θ hθ using hθ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ := fun T ↦
    _root_.GlobalTheory.Obs.exists_isSig R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'',
      α.KerQ y ∧ σ T'' y = θ T T' T'' a b (w.1 T) := fun T T' T'' a b ↦
    (_root_.GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
      (L.ker T'') (σ T'') (hσ T'')).2.2.2 _ ((hθ T T' T'' a b).mem _)
  choose z hzK hzσ using hz
  have key : ∀ (T T' T'' T''' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T''') (x : Ω[F.obj T⁄R₀]),
      L.ρ c (θ T T' T'' a b x) + θ T T'' T''' (a ≫ b) c x =
        θ T T' T''' a (b ≫ c) x + θ T' T'' T''' b c (p1 F a x) := by
    intro T T' T'' T''' a b c x
    have h1 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T'') (L.B T''') _ _ _
      (hθ T T' T'' a b)).1 (L.ρ c)
    have s1 := (_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h1).2.1 (hθ T T'' T''' (a ≫ b) c)
    have h2 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T''') (L.B T''') _ _ _
      (hθ T' T'' T''' b c)).2 (L.ρ a) (mp F a) (L.nat a)
    have s2 := (_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h2).2.1 (hθ T T' T''' a (b ≫ c))
    rw [Category.assoc] at s1
    rw [AlgHom.comp_assoc] at s2
    have e := (_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ (L.ρ (a ≫ b ≫ c)) _ _ s1).2.2.1 s2
    have ex := DFunLike.congr_fun e x
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply] at ex
    exact ex.trans (add_comm _ _)
  have hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F) := by
    intro T T' T'' T''' a b c
    haveI := L.smooth T'''
    haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _
    have nat := _root_.GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'')
      (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''')
      (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')
    have em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y := fun _ ↦ rfl
    rw [← sub_eq_zero]
    apply _root_.GlobalTheory.Obs.sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''')
      (L.surj T''') (L.ker T''') (σ T''') (hσ T''')
    · have k1 := nat.2 _ (hzK T T' T'' a b)
      have k2 := hzK T T'' T''' (a ≫ b) c
      have k3 := hzK T T' T''' a (b ≫ c)
      have k4 := hzK T' T'' T''' b c
      unfold Aug.KerQ at k1 k2 k3 k4 ⊢
      rw [em]
      simp only [map_sub, map_add (f := _), k1, k2, k3, k4, sub_self, add_zero]
    · rw [em, map_sub, map_add (f := _), map_add (f := _), ← (nat.1 _), hzσ, hzσ, hzσ, hzσ, w.2 a, key, sub_self]
  exact ⟨H2.mk _ ⟨_, hZ⟩, θ, σ, ⟨_, hZ⟩, hθ, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, hzσ T T' T'' a b⟩⟩

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorPrimeToLFiniteAdele
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.AdeleDen

theorem val_nat {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    Valued.v ((n : w.adicCompletion E)) = w.valuation E (algebraMap (𝓞 E) E (n : 𝓞 E)) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w]
  congr 1
  rw [map_natCast]
  exact (map_natCast (algebraMap E (w.adicCompletion E)) n).symm

theorem val_nat_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    Valued.v ((n : w.adicCompletion E)) ≤ 1 := by
  rw [val_nat]; exact w.valuation_le_one _

theorem exists_nat_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (l : 𝓞 E) ∉ w.asIdeal) :
    ∃ m : ℕ, ¬ l ∣ m ∧ (m : 𝓞 E) ∈ w.asIdeal := by
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  obtain ⟨k, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  refine ⟨m, hm, ?_⟩
  have h := Ideal.absNorm_mem w.asIdeal
  rw [e] at h
  push_cast at h
  rcases w.isPrime.mem_or_mem h with h | h
  · exact absurd (w.isPrime.mem_of_pow_mem _ h) hw
  · exact h

theorem exists_local {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (l : 𝓞 E) ∉ w.asIdeal) (x : w.adicCompletion E) :
    ∃ m : ℕ, ¬ l ∣ m ∧ Valued.v ((m : w.adicCompletion E) * x) ≤ 1 := by
  obtain ⟨m, hm, hmw⟩ := exists_nat_mem hl w hw
  by_cases hx : Valued.v x = 0
  · exact ⟨m, hm, by simp [hx]⟩
  have h1 : Valued.v ((m : w.adicCompletion E)) < 1 := by
    rw [val_nat]; exact (w.valuation_lt_one_iff_mem _).mpr hmw
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h1 (Units.mk0 _ (inv_ne_zero hx))
  refine ⟨m ^ n, fun h => hm (hl.dvd_of_dvd_pow h), ?_⟩
  rw [Nat.cast_pow, map_mul, map_pow]
  calc _ ≤ (Valued.v x)⁻¹ * Valued.v x := mul_le_mul_left hn.le _
    _ = 1 := inv_mul_cancel₀ hx

theorem exists_den_prime_to : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (z : Af E), l.Prime → (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v (z w) ≤ 1) → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (Af E) (M : E) * z) w) ≤ 1 := by
  intro E _ _ l z hl hz
  have key : ∀ w : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, ¬ l ∣ m ∧
      Valued.v ((m : w.adicCompletion E) * z w) ≤ 1 := by
    intro w
    by_cases hw : (l : 𝓞 E) ∈ w.asIdeal
    · exact ⟨1, hl.not_dvd_one, by simpa using hz w hw⟩
    · exact exists_local hl w hw _
  choose m hm hmz using key
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ z w ∈ w.adicCompletionIntegers E}.Finite :=
    Filter.eventually_cofinite.mp z.2
  refine ⟨∏ w ∈ hfin.toFinset, m w, ?_, fun w => ?_⟩
  · have hprod : ∀ s : Finset (HeightOneSpectrum (𝓞 E)), ¬ l ∣ ∏ w ∈ s, m w := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hl.not_dvd_one
      | @insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        intro h
        rcases hl.dvd_mul.mp h with h | h
        · exact hm a h
        · exact ih h
    exact hprod _
  · have e : ∀ M : ℕ, (algebraMap E (Af E) (M : E) * z) w = (M : w.adicCompletion E) * z w := by
      intro M
      rw [← map_natCast (algebraMap E (w.adicCompletion E)) M]
      rfl
    rw [e]
    by_cases hw : w ∈ hfin.toFinset
    · rw [← Finset.prod_erase_mul _ _ hw, Nat.cast_mul, mul_assoc, map_mul]
      exact mul_le_one' (val_nat_le _ _) (hmz w)
    · have : z w ∈ w.adicCompletionIntegers E := by simpa using hw
      rw [map_mul]
      exact mul_le_one' (val_nat_le _ _) this

end GlobalTheory.HilbFam.AdeleDen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentCocycleDefectOfCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescDefect

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

theorem compat_gm {L : LB X} {φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ} (hC : DescCompat f L φ)
    {T : Scheme.{0}} (s : T ⟶ pullback f f) (t : T) (i i' j j' : L.ι)
    (hi : pullback.fst f f (s t) ∈ L.U i) (hi' : pullback.fst f f (s t) ∈ L.U i')
    (hj : pullback.snd f f (s t) ∈ L.U j) (hj' : pullback.snd f f (s t) ∈ L.U j') :
    gm s t _ (φ i' j') =
      gm (s ≫ pullback.fst f f) t _ (L.g i i') * gm s t _ (φ i j) * gm (s ≫ pullback.snd f f) t _ (L.g j' j) := by
  have l₁ : chart f L i j ⊓ chart f L i' j' ≤ pullback.fst f f ⁻¹ᵁ (L.U i ⊓ L.U i') :=
    fun z hz => ⟨hz.1.1, hz.2.1⟩
  have l₂ : chart f L i j ⊓ chart f L i' j' ≤ pullback.snd f f ⁻¹ᵁ (L.U j' ⊓ L.U j) :=
    fun z hz => ⟨hz.2.2, hz.1.2⟩
  have hO : res (inf_le_right : chart f L i j ⊓ chart f L i' j' ≤ _) (φ i' j') =
      res l₁ (pullU (pullback.fst f f) _ (L.g i i')) * res inf_le_left (φ i j) *
        res l₂ (pullU (pullback.snd f f) _ (L.g j' j)) := by
    apply unit_ext
    intro z hz
    rw [map_mul, map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz,
      gm_pull (𝟙 _) (pullback.fst f f) z _ (l₁ hz) _, gm_pull (𝟙 _) (pullback.snd f f) z _ (l₂ hz) _,
      Category.id_comp, Category.id_comp]
    exact hC z i i' j j' hz.1.1 hz.2.1 hz.1.2 hz.2.2
  have hst : s t ∈ chart f L i j ⊓ chart f L i' j' := ⟨⟨hi, hj⟩, ⟨hi', hj'⟩⟩
  have e := congrArg (gm s t (chart f L i j ⊓ chart f L i' j')) hO
  rw [map_mul, map_mul, gm_res _ t _ hst, gm_res _ t _ hst, gm_res _ t _ hst, gm_res _ t _ hst,
    gm_pull s (pullback.fst f f) t _ (l₁ hst) _, gm_pull s (pullback.snd f f) t _ (l₂ hst) _] at e
  exact e

theorem defect_exists : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    L.IsLB → DescCompat f L φ → ∃ D : Γ(Triple f, ⊤)ˣ, Defect f L φ D := by
  intro X Y f L φ hL hC
  set a := pullback.fst (pullback.snd f f) (pullback.fst f f) with ha
  set b := pullback.snd (pullback.snd f f) (pullback.fst f f) with hb
  have hab : a ≫ pullback.snd f f = b ≫ pullback.fst f f := pullback.condition
  have hca : pr13 f ≫ pullback.fst f f = a ≫ pullback.fst f f := pullback.lift_fst _ _ _
  have hcb : pr13 f ≫ pullback.snd f f = b ≫ pullback.snd f f := pullback.lift_snd _ _ _
  have pab : ∀ x, pullback.snd f f (a x) = pullback.fst f f (b x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hab
    simpa only [Scheme.Hom.comp_apply] using this
  have pca : ∀ x, pullback.fst f f (pr13 f x) = pullback.fst f f (a x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hca
    simpa only [Scheme.Hom.comp_apply] using this
  have pcb : ∀ x, pullback.snd f f (pr13 f x) = pullback.snd f f (b x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hcb
    simpa only [Scheme.Hom.comp_apply] using this

  have K : ∀ (T : Scheme.{0}) (s : T ⟶ Triple f) (t : T) (i j k i' j' k' : L.ι),
      pullback.fst f f (a (s t)) ∈ L.U i → pullback.fst f f (a (s t)) ∈ L.U i' →
      pullback.snd f f (a (s t)) ∈ L.U j → pullback.snd f f (a (s t)) ∈ L.U j' →
      pullback.snd f f (b (s t)) ∈ L.U k → pullback.snd f f (b (s t)) ∈ L.U k' →
      gm (s ≫ a) t _ (φ i j) * gm (s ≫ b) t _ (φ j k) * (gm (s ≫ pr13 f) t _ (φ i k))⁻¹ =
        gm (s ≫ a) t _ (φ i' j') * gm (s ≫ b) t _ (φ j' k') * (gm (s ≫ pr13 f) t _ (φ i' k'))⁻¹ := by
    intro T s t i j k i' j' k' hi hi' hj hj' hk hk'
    have hjb : pullback.fst f f (b (s t)) ∈ L.U j := pab (s t) ▸ hj
    have hjb' : pullback.fst f f (b (s t)) ∈ L.U j' := pab (s t) ▸ hj'
    have hic : pullback.fst f f (pr13 f (s t)) ∈ L.U i := (pca (s t)).symm ▸ hi
    have hic' : pullback.fst f f (pr13 f (s t)) ∈ L.U i' := (pca (s t)).symm ▸ hi'
    have hkc : pullback.snd f f (pr13 f (s t)) ∈ L.U k := (pcb (s t)).symm ▸ hk
    have hkc' : pullback.snd f f (pr13 f (s t)) ∈ L.U k' := (pcb (s t)).symm ▸ hk'
    have E1 := compat_gm f hC (s ≫ a) t i i' j j' hi hi' hj hj'
    have E2 := compat_gm f hC (s ≫ b) t j j' k k' hjb hjb' hk hk'
    have E3 := compat_gm f hC (s ≫ pr13 f) t i i' k k' hic hic' hkc hkc'
    have hc := gm_cocycle hL (s ≫ b ≫ pullback.fst f f) t (i := j') (j := j) (k := j') hjb' hjb hjb'
    rw [gm_self hL _ t hjb'] at hc
    simp only [Category.assoc] at E1 E2 E3
    rw [hca, hcb] at E3
    rw [hab] at E1
    rw [E1, E2, E3]
    generalize gm (s ≫ b ≫ pullback.fst f f) t _ (L.g j' j) = G2 at hc ⊢
    generalize gm (s ≫ b ≫ pullback.fst f f) t _ (L.g j j') = G3 at hc ⊢
    have : G3 = G2⁻¹ := eq_inv_of_mul_eq_one_right hc
    subst this
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  let V : L.ι × L.ι × L.ι → (Triple f).Opens := fun p =>
    a ⁻¹ᵁ chart f L p.1 p.2.1 ⊓ b ⁻¹ᵁ chart f L p.2.1 p.2.2 ⊓ pr13 f ⁻¹ᵁ chart f L p.1 p.2.2
  have la : ∀ p, V p ≤ a ⁻¹ᵁ chart f L p.1 p.2.1 := fun p => inf_le_left.trans inf_le_left
  have lb : ∀ p, V p ≤ b ⁻¹ᵁ chart f L p.2.1 p.2.2 := fun p => inf_le_left.trans inf_le_right
  have lc : ∀ p, V p ≤ pr13 f ⁻¹ᵁ chart f L p.1 p.2.2 := fun p => inf_le_right
  have memV : ∀ (x : Triple f) (i j k : L.ι), pullback.fst f f (a x) ∈ L.U i → pullback.snd f f (a x) ∈ L.U j →
      pullback.snd f f (b x) ∈ L.U k → x ∈ V (i, j, k) := fun x i j k hi hj hk =>
    ⟨⟨⟨hi, hj⟩, ⟨(show pullback.fst f f (b x) ∈ L.U j from pab x ▸ hj), hk⟩⟩,
      ⟨(show pullback.fst f f (pr13 f x) ∈ L.U i from (pca x).symm ▸ hi),
        (show pullback.snd f f (pr13 f x) ∈ L.U k from (pcb x).symm ▸ hk)⟩⟩
  let u : ∀ p, Γ(Triple f, V p)ˣ := fun p =>
    res (la p) (pullU a _ (φ p.1 p.2.1)) * res (lb p) (pullU b _ (φ p.2.1 p.2.2)) *
      (res (lc p) (pullU (pr13 f) _ (φ p.1 p.2.2)))⁻¹
  have hu : ∀ (T : Scheme.{0}) (s : T ⟶ Triple f) (t : T) (p : L.ι × L.ι × L.ι), s t ∈ V p →
      gm s t (V p) (u p) = gm (s ≫ a) t _ (φ p.1 p.2.1) * gm (s ≫ b) t _ (φ p.2.1 p.2.2) *
        (gm (s ≫ pr13 f) t _ (φ p.1 p.2.2))⁻¹ := by
    intro T s t p hp
    simp only [u, map_mul, map_inv]
    rw [gm_res _ t _ hp, gm_res _ t _ hp, gm_res _ t _ hp, gm_pull s a t _ (la p hp) _,
      gm_pull s b t _ (lb p hp) _, gm_pull s (pr13 f) t _ (lc p hp) _]
  obtain ⟨D, hD⟩ := glue_unit ⊤ V (fun _ => le_top) (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (a x))
      obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (a x))
      obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (b x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j, k), memV x i j k hi hj hk⟩) u (fun p p' x hx => by
      rw [hu _ (𝟙 _) x p hx.1, hu _ (𝟙 _) x p' hx.2]
      exact K _ (𝟙 _) x _ _ _ _ _ _ hx.1.1.1.1 hx.2.1.1.1 hx.1.1.1.2 hx.2.1.1.2 hx.1.1.2.2 hx.2.1.2.2)
  refine ⟨D, fun T r t i j k hi hj hk => ?_⟩
  have hm := memV (r t) i j k hi hj hk
  rw [← gm_res r t (fun _ _ => trivial : V (i, j, k) ≤ ⊤) hm D, hD (i, j, k), hu T r t (i, j, k) hm]
  exact inv_mul_cancel_right _ _

end GlobalTheory.DescDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagEndIsMonHom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj GrpObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

def diagPrecomp {T : Scheme.{0}} {X Y M : Over T} [MonObj M] (f : X ⟶ Y) : (Y ⟶ M) →* (X ⟶ M) where
  toFun := (f ≫ ·)
  map_one' := by
    change f ≫ toUnit Y ≫ η = toUnit X ≫ η
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit Y)]
  map_mul' g h := by
    change f ≫ lift g h ≫ μ = lift (f ≫ g) (f ≫ h) ≫ μ
    rw [← Category.assoc, comp_lift]

theorem exists_diagEnd_isMonHom (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Scheme.{0})
    (P : PolAV T) (u : T ⟶ F.X) (h : SharpOver F W P u) :
    ∃ ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A), IsDiagEnd F W P u ε ∧ ∀ E, IsMonHom (ε E) := by
  obtain ⟨c, hc, pr, hpr, huniq, hL⟩ := h
  choose ε hε _ using fun E : Matrix (Fin 8) (Fin 8) ℤ =>
    huniq P.A (fun a => ((List.finRange 8).map fun b => pr b ^ E a b).prod)
  have ext : ∀ (T' : Over T) (x x' : T' ⟶ P.A), (∀ a, x ≫ pr a = x' ≫ pr a) → x = x' := fun T' x x' hx =>
    (huniq T' (fun a => x' ≫ pr a)).unique hx (fun _ => rfl)
  refine ⟨ε, ⟨c, hc, pr, hpr, huniq, hL, hε⟩, fun E => ?_⟩
  have key : ∀ (T' : Over T) (x : T' ⟶ P.A) (a : Fin 8),
      (x ≫ ε E) ≫ pr a = ((List.finRange 8).map fun b => (x ≫ pr b) ^ E a b).prod := by
    intro T' x a
    rw [Category.assoc, hε]
    change diagPrecomp (M := c.A) x _ = _
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    exact map_zpow (diagPrecomp (M := c.A) x) (pr b) (E a b)
  refine isMonHom_of_mul _ fun T' x z => ext T' _ _ fun a => ?_
  have hm : ∀ (b : Fin 8) (x z : T' ⟶ P.A), (x * z) ≫ pr b = (x ≫ pr b) * (z ≫ pr b) := fun b x z =>
    map_mul (IsMonHom.monoidHom (pr b) T') x z
  have hm' : ((x ≫ ε E) * (z ≫ ε E)) ≫ pr a = ((x ≫ ε E) ≫ pr a) * ((z ≫ ε E) ≫ pr a) :=
    map_mul (IsMonHom.monoidHom (pr a) T') (x ≫ ε E) (z ≫ ε E)
  rw [key, hm', key, key, ← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  rw [hm, mul_zpow]

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceEquivOfRingEquivOverConstants
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem placeEquiv_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∃ Φ : Place c ≃ Place c', ∀ E : Place c, (∀ a, e a ∈ (Φ E).ring ↔ a ∈ E.ring) ∧ (∀ a, (Φ E).ord (e a) = E.ord a) ∧ (∀ φ : K →₀ ℚ, (Φ E).ordQ (Finsupp.mapDomain e φ) = E.ordQ φ) ∧ ∀ (n : ℕ) (x : Fin n → K), TrBasis c x → (Φ E).formOrd (dForm c' (e ∘ x)) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm c x) := by
  intro k K K' _ _ _ _ c c' e he
  refine ⟨⟨RingEquivTransport.place e he,
    RingEquivTransport.place e.symm (RingEquivTransport.symm_apply e he),
    RingEquivTransport.place_symm_place e he, RingEquivTransport.place_place_symm e he⟩,
    fun E => ⟨RingEquivTransport.apply_mem_place e he E, RingEquivTransport.ord_place e he E,
      RingEquivTransport.ordQ_place e he E, fun n x _ => ?_⟩⟩
  have hd : dForm c' (e ∘ x) = TopForm.formMap n e.toRingHom (RingHom.ext he) (dForm c x) :=
    (TopForm.formMap_dForm e.toRingHom (RingHom.ext he) x).symm
  change (RingEquivTransport.place e he E).formOrd _ = _
  rw [hd]
  exact RingEquivTransport.formOrd_place e he E _

end GlobalTheory.FieldPair
end

