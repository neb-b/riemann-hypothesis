module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsIntegralZpowOfPowEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem isIntegral_of_pow_eq_one {F : Type} [Field F] {z : F} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) :
    IsIntegral ℤ z := by
  refine IsIntegral.of_pow hN ?_
  rw [hz]
  exact isIntegral_one

theorem isIntegral_zpow_of_pow_eq_one {F : Type} [Field F] {z : F} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) (a : ℤ) :
    IsIntegral ℤ (z ^ a) := by

  refine GlobalTheory.PlaceInt.isIntegral_of_pow_eq_one hN ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm a, zpow_mul, zpow_natCast, hz, one_zpow]

private theorem isIntegral_int_ringHom_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a : A}
    (h : IsIntegral ℤ a) : IsIntegral ℤ (f a) :=
  h.map f.toIntAlgHom

theorem datum_isIntegral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ ph ψ x₀, d.PhiPin ph ψ x₀ → ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ x₀ hpin x0 q
  obtain ⟨-, hM, -, -, hII, -⟩ := id hd
  obtain ⟨hloc, hsupp, hequi, hone, hspan0, hsum⟩ := hpin
  have hpd : 0 < d.pd := by
    rcases Nat.eq_zero_or_pos d.pd with h | h
    · have h3 := d.l₂.three_le
      rw [hM, h, mul_zero] at h3
      omega
    · exact h

  have hI : d.I ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot, sup_bot_eq] at hII
    exact bot_ne_top hII
  have : Finite (𝓞 E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot d.I hI
  have := Dw.fin
  have := Dw.proj
  obtain ⟨eI⟩ := GlobalTheory.HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I (Dw.p + Dw.q) Dw.rank
  have : Finite (LaI Xo c d) := Finite.of_equiv _ eI.symm.toEquiv
  have : Finite (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) :=
    Finite.of_injective (fun e : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d => (e : LaI Xo c d → LaI Xo c d))
      (fun a b h => LinearEquiv.ext (congrFun h))

  have hph : ∀ x, IsIntegral ℤ (ph x) := by
    intro x
    by_cases h0 : ph x = 0
    · rw [h0]
      exact isIntegral_zero
    have hspan := hsupp x h0
    obtain ⟨-, htrans, adj, -, hadj⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
    let pad : (Fin n → LaJ Xo c d) → Fin (Dw.p + Dw.q) → LaJ Xo c d :=
      fun z i => if h : i.val < n then z ⟨i.val, h⟩ else 0
    have hpadv : ∀ z i (h : i.val < n), pad z i = z ⟨i.val, h⟩ := fun z i h => dif_pos h
    have hpad : ∀ z : Fin n → LaJ Xo c d, Submodule.span (𝓞 E) (z '' {b | b.val < Dw.p + Dw.q}) = ⊤ →
        Submodule.span (𝓞 E) (Set.range (pad z)) = ⊤ := by
      intro z hz
      rw [eq_top_iff, ← hz]
      apply Submodule.span_mono
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, hpadv z _ b.isLt⟩
    obtain ⟨g, hg, -⟩ := htrans (pad x₀) (pad x) (hpad x₀ hspan0) (hpad x hspan)
    have h1 := hequi (adj g) g ((hadj (adj g) g).mpr rfl) x₀
    rw [hone, _root_.mul_one] at h1
    have h2 : ph x = ph (fun b => g (x₀ b)) := by
      apply hloc
      intro b hb
      have hb' := hg ⟨b.val, hb⟩
      rw [hpadv x₀ _ b.isLt, hpadv x _ b.isLt] at hb'
      exact hb'.symm
    rw [h2, h1]
    obtain ⟨m, hm, hpow⟩ :=
      isOfFinOrder_iff_pow_eq_one.mp (ψ.isOfFinOrder (isOfFinOrder_of_finite (adj g))).inv
    refine GlobalTheory.PlaceInt.isIntegral_of_pow_eq_one hm ?_
    rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]

  have hz : IsIntegral ℤ (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b))) :=
    GlobalTheory.PlaceInt.isIntegral_zpow_of_pow_eq_one (N := l.M) (by have := l.three_le; omega)
      (GlobalTheory.DatumInverseCharacter.root_pow c dvd_rfl) _

  have hφ : IsIntegral ℤ (d.φδ q) := by
    have he : IsIntegral ℤ (d.eF (d.φδ q)) := by
      rw [hsum q]
      refine finsum_induction (fun y => IsIntegral ℤ y) isIntegral_zero
        (fun a b ha hb => ha.add hb) (fun x => ?_)
      refine (isIntegral_int_ringHom_apply d.eF.toRingHom (hph x)).mul ?_
      exact GlobalTheory.PlaceInt.isIntegral_zpow_of_pow_eq_one hpd
        (GlobalTheory.DatumInverseCharacter.root_pow d.c₂ (Dvd.intro_left _ hM.symm)) _
    have hb := isIntegral_int_ringHom_apply d.eF.symm.toRingHom he
    simpa using hb
  exact isIntegral_int_ringHom_apply d.eF.toRingHom (hz.mul hφ)

end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMul
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PullComp

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem isNormPull_comp (φ ψ : A ⟶ A) [IsMonHom ψ] (a b c : ℤ) {T : Over S} {s : LB.Sec (LPow A L.L a T)}
    {s' : LB.Sec (LPow A L.L b T)} {s'' : LB.Sec (LPow A L.L c T)} (h : IsNormPull A L φ b a s s')
    (h' : IsNormPull A L ψ c b s' s'') : IsNormPull A L (ψ ≫ φ) c a s s'' := by
  have hL := L.isLB
  have he : eSec A ≫ ψ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨β₀, β, hβ₀, nβ, cβ, tβ⟩ := h
  obtain ⟨δ₀, δ, hδ₀, nδ, cδ, tδ⟩ := h'
  obtain ⟨α₀, hα₀, hv₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, (ψ ≫ φ).left]) (ε' := ![c, -a])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, Over.comp_left, zpow_neg]
      rw [_root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L.L _ _ _ _ δ₀ (LB.pullGen L.L _ _ β₀ ψ.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hδ₀ (DVR.pullGen_isGen _ _ _ _ hβ₀ _))
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ≫ ψ ≫ φ).left]) (ε' := ![c, -a])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ c) (Category.comp_id _)
      · rfl)
    (LB.pullGen L.L ![𝟙 A.left, (ψ ≫ φ).left] ![c, -a] α₀ (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  refine ⟨α₀, α, hα₀, corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => hv _ _ y J hJ,
    ThetaLin.isTwistPull_of_sval A hL hα fun y J hJ => ?_⟩
  · have e₁ := val_corr hJ nβ (𝟙 _)
    have e₂ := val_corr hJ nδ (𝟙 _)
    rw [val_pull hJ, val_mul hJ, UT.PullMul.val_rigPow, UT.PullMul.val_rigPow] at e₁ e₂
    rw [val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, he, e₁, e₂, val_mul hJ,
      UT.PullMul.val_rigPow, UT.PullMul.val_rigPow, zpow_neg _ b, _root_.mul_assoc, inv_mul_cancel_left]
  · have e₁ : (endOver A T ψ).left ≫ (snd T A).left = (snd T A).left ≫ ψ.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    have e₂ : (endOver A T ψ).left ≫ (endOver A T φ).left = (endOver A T (ψ ≫ φ)).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]
    rw [ThetaLin.sval_of_isTwistPull A tδ _ y hJ, ThetaLin.sval_of_isTwistPull A tβ _ y hJ, val_corr hJ cδ,
      val_corr hJ cβ, hv _ _ y J hJ, val_pull hJ, val_pull hJ, val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ,
      Units.val_mul, _root_.mul_assoc]
    simp only [Category.assoc, e₁, e₂]

theorem pulls_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (a b : 𝓞 E) (k k' k'' : ℕ) (F : SecN Xo x k) (F' : SecN Xo x k') (F'' : SecN Xo x k''), Pulls Xo a F F' → Pulls Xo b F' F'' → Pulls Xo (a * b) F F'' := by
  intro E _ _ _ H Dw l Xo S _ x a b k k' k'' F F' F'' h h'
  have := Xo.univ.t.act.hom b
  unfold Pulls
  rw [_root_.mul_comm a b, Xo.univ.t.act.mul]
  exact isNormPull_comp _ _ _ _ _ _ h h'

end GlobalTheory.PullComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPrincipalIdealRingLoc
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PlaceInt.LocBasis
open NumberField Module
open scoped nonZeroDivisors

theorem exists_basis_up_to {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A] [Algebra A E]
    [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : ℕ} (L : Submodule O (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ (s : S) (b : Fin n → Fin n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (Fin n → E) := Submodule.span A (L : Set (Fin n → E)) with hM
  have : Submodule.IsFullLattice E M :=
    { toIsLattice := Submodule.IsLattice.of_fg E <| by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq E M).trans (Module.finrank_fintype_fun_eq_card E))
  haveI : Module.Finite A M := Submodule.IsLattice.finite E M
  let c : Basis (Fin n) A M := Module.finBasisOfFinrankEq A M hrk
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : Fin n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (Fin n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : Fin n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis (Fin n) A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : Fin n → E) = (t i : O) • (c i : Fin n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : Fin n → Fin n → E := fun i => (c' i : Fin n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsFullLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsFullLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

def primeTo (R : Type) [CommRing R] (m : ℕ) : Submonoid R where
  carrier := {x | ∃ k : ℕ, k ≠ 0 ∧ Nat.Coprime k m ∧ x = (k : R)}
  one_mem' := ⟨1, one_ne_zero, Nat.coprime_one_left m, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha0, ha, rfl⟩ ⟨b, hb0, hb, rfl⟩
    exact ⟨a * b, mul_ne_zero ha0 hb0, Nat.Coprime.mul_left ha hb, by simp⟩

theorem exists_prime_mem {R : Type} [CommRing R] (Q : Ideal R) (hQ : Q.IsPrime) (a : ℕ) (ha : a ≠ 0)
    (h : (a : R) ∈ Q) : ∃ p : ℕ, p.Prime ∧ (p : R) ∈ Q := by
  induction a using induction_on_primes with
  | zero => exact absurd rfl ha
  | one => exact absurd ((Ideal.eq_top_iff_one Q).2 (by simpa using h)) hQ.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hQ.mem_or_mem h with h | h
    · exact ⟨p, hp, h⟩
    · exact ih (by rintro rfl; simp at ha) h

theorem isPrincipalIdealRing_loc (E : Type) [Field E] [NumberField E] (m : ℕ) (hm : 0 < m)
    (hS : primeTo (𝓞 E) m ≤ (𝓞 E)⁰) (A : Type) [CommRing A] [IsDomain A] [Algebra (𝓞 E) A]
    [IsLocalization (primeTo (𝓞 E) m) A] : IsPrincipalIdealRing A := by
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain (𝓞 E) hS A
  have hinj : Function.Injective (algebraMap (𝓞 E) A) := IsLocalization.injective A hS
  have hm0 : (m : A) ≠ 0 := by
    rw [← map_natCast (algebraMap (𝓞 E) A), map_ne_zero_iff _ hinj]
    exact_mod_cast hm.ne'
  have hI : (Ideal.span {(m : A)}) ≠ 0 := by simpa using hm0
  apply IsPrincipalIdealRing.of_finite_primes
  apply (((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset
  intro P hP
  have hP' : P.IsPrime := hP
  by_cases hb : P = ⊥
  · exact Or.inl hb
  refine Or.inr ⟨⟨P, hP', hb⟩, ?_, rfl⟩
  set Q := P.comap (algebraMap (𝓞 E) A) with hQ
  have hQb : Q ≠ ⊥ := by
    intro h
    apply hb
    rw [← IsLocalization.map_under (primeTo (𝓞 E) m) A P]
    change Q.map _ = ⊥
    rw [h, Ideal.map_bot]
  have h1 : ((Ideal.absNorm Q : ℕ) : A) ∈ P := by
    have := Ideal.absNorm_mem Q
    rw [hQ, Ideal.mem_comap, map_natCast] at this
    exact this
  obtain ⟨p, hp, hpP⟩ := exists_prime_mem P hP' _ (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) h1
  have hpm : p ∣ m := by
    by_contra hn
    have hu := IsLocalization.map_units A (⟨(p : 𝓞 E), p, hp.ne_zero, (Nat.Prime.coprime_iff_not_dvd hp).2 hn,
      rfl⟩ : primeTo (𝓞 E) m)
    simp only [map_natCast] at hu
    exact hP'.ne_top (Ideal.eq_top_of_isUnit_mem _ hpP hu)
  obtain ⟨c, rfl⟩ := hpm
  simp only [Set.mem_setOf_eq, Ideal.dvd_span_singleton, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.PlaceInt.LocBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.LocBasis

theorem exists_matrix_primeTo : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), 0 < N → L ≤ stdLat E n → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ L → ∀ m : ℕ, 0 < m → ∃ (k₁ : ℕ) (g : Matrix (Fin n) (Fin n) (𝓞 E)), Nat.Coprime k₁ m ∧ g.det ≠ 0 ∧ (∀ v ∈ stdLat E n, (g.map (algebraMap (𝓞 E) E)).mulVec v ∈ L) ∧ ∀ w ∈ L, ∃ v ∈ stdLat E n, (k₁ : E) • w = (g.map (algebraMap (𝓞 E) E)).mulVec v := by
  intro E _ _ n L N hN hle hNL m hm
  classical
  have hmem : ∀ v : Fin n → E, v ∈ stdLat E n ↔ ∃ u : Fin n → 𝓞 E, v = fun i => algebraMap (𝓞 E) E (u i) := fun v => by
    simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    constructor
    · intro h
      choose u hu using h
      exact ⟨u, funext fun i => (hu i).symm⟩
    · rintro ⟨u, rfl⟩ i
      exact ⟨u i, rfl⟩
  have hS : primeTo (𝓞 E) m ≤ nonZeroDivisors (𝓞 E) := by
    rintro _ ⟨k, hk, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)
  let A := Localization.subalgebra E (primeTo (𝓞 E) m) hS
  have : IsPrincipalIdealRing A := isPrincipalIdealRing_loc E m hm hS A
  have hstd : (stdLat E n).FG := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  have hfg : L.FG := hstd.of_le hle
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : (Pi.basisFun E (Fin n) i) ∈ stdLat E n :=
      (hmem _).2 ⟨Pi.single i 1, funext fun j => by by_cases h : j = i <;> simp [h, Pi.single_apply]⟩
    have h2 := hNL (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1)
    have h3 := Submodule.smul_mem (Submodule.span E (L : Set (Fin n → E))) (N : E)⁻¹ (Submodule.subset_span h2)
    rwa [← algebraMap_smul E (N : 𝓞 E), smul_smul, map_natCast, inv_mul_cancel₀ hN0, one_smul] at h3
  obtain ⟨⟨_, k, hk0, hk, rfl⟩, b, hli, hb, hw⟩ := exists_basis_up_to (A := A) (primeTo (𝓞 E) m) L hfg hsp
  choose u hu using fun j => (hmem (b j)).1 (hle (hb j))
  let g : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun i j => u j i
  have hg : ∀ a : Fin n → 𝓞 E, (g.map (algebraMap (𝓞 E) E)).mulVec (fun i => algebraMap (𝓞 E) E (a i)) =
      ∑ j, a j • b j := fun a => by
    funext i
    simp only [Matrix.mulVec, dotProduct, g, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu j, Algebra.smul_def, mul_comm]
  refine ⟨k, g, hk, ?_, ?_, ?_⟩
  · have hcol : (g.map (algebraMap (𝓞 E) E)).col = b := by
      funext j i
      rw [hu j]; rfl
    have hunit : IsUnit (g.map (algebraMap (𝓞 E) E)) :=
      Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
    intro h0
    have := ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
    apply this
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · intro v hv
    obtain ⟨a, rfl⟩ := (hmem v).1 hv
    rw [hg]
    exact Submodule.sum_mem _ fun j _ => L.smul_mem _ (hb j)
  · intro w hwL
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw w hwL)
    refine ⟨_, (hmem _).2 ⟨a, rfl⟩, ?_⟩
    rw [hg, ha]
    change _ = (k : 𝓞 E) • w
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
end GlobalTheory.PlaceInt.LocBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumSupportCMul
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt


open GlobalTheory.NabLinear in
theorem nab_smul_secN {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) (F F' : SecN Xo y.x k) (r : S)
    (hF : ∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) :
    ∀ α, nab y (k : ℤ) F' α = r * nab y (k : ℤ) F α := by
  intro α
  let _ : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  obtain ⟨C, hex, hval⟩ := hnab.2 S y
  obtain ⟨f, hf⟩ := hex k F
  have hf' : IsGerm y C.d C.x C.B.A.act C.e C.wP k F' (MvPowerSeries.C r * f) := by
    unfold IsGerm at hf ⊢
    intro m
    obtain ⟨F₁, τ, h1, hc, hv⟩ := hf m
    obtain ⟨F₂, h2⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (jBase y C.d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F'
    refine ⟨F₂, τ, h2, hc, ?_⟩
    have hs := GlobalTheory.NabLinear.isValueAt_scale Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (jBase y C.d m 1) hF h1 h2 hv
    convert hs using 1
    have hj : (jBase y C.d m 1).left = spMap (algebraMap S (Jet S (Fin 1 × Fin C.d) m)) := rfl
    rw [hj, GlobalTheory.NabLinear.appTop_toΓ, ← map_mul, ← GlobalTheory.NabLinear.psJet_C]
    congr 1
    clear hval hex hs h1 h2 hv hc hF hnab hj F₁ F₂ hf
    unfold psJet
    rw [← map_mul]
    congr 1
    unfold psTrunc
    have h0 : (0 : Fin 1 × Fin C.d →₀ ℕ) ∈ degLE m := by
      unfold degLE
      simp
      exact ⟨fun _ => 0, by ext; simp⟩
    have hC : ∑ e ∈ degLE m, MvPolynomial.monomial e
        (MvPowerSeries.coeff e (MvPowerSeries.C r : MvPowerSeries (Fin 1 × Fin C.d) S)) =
        MvPolynomial.monomial 0 r := by
      rw [Finset.sum_eq_single_of_mem 0 h0 (fun e _ he => by rw [MvPowerSeries.coeff_C, if_neg he, map_zero]),
        MvPowerSeries.coeff_C, if_pos rfl]
    rw [hC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPolynomial.monomial_mul, zero_add]
  exact (hval k F' _ hf' α).trans ((GlobalTheory.NabLinear.nabVal_C_mul C.B C.h H.w0 k r f C.uvec _).trans
    (congrArg (r * ·) (hval k F f hf α).symm))

theorem sum_support_C_mul {σ K S : Type} [CommRing K] [CommRing S] [Algebra K S] (P : MvPolynomial σ K) (s : K)
    (g : (σ →₀ ℕ) → S) :
    ∑ m ∈ (MvPolynomial.C s * P).support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m =
      algebraMap K S s * ∑ m ∈ P.support, algebraMap K S (P.coeff m) * g m := by
  classical
  have hsub : (MvPolynomial.C s * P).support ⊆ P.support := by
    rw [MvPolynomial.C_mul']
    exact MvPolynomial.support_smul
  calc ∑ m ∈ (MvPolynomial.C s * P).support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m
      = ∑ m ∈ P.support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m := by
        apply Finset.sum_subset hsub
        intro m _ hm
        rw [MvPolynomial.mem_support_iff, not_not] at hm
        rw [hm, map_zero, zero_mul]
    _ = algebraMap K S s * ∑ m ∈ P.support, algebraMap K S (P.coeff m) * g m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [MvPolynomial.coeff_C_mul, map_mul, _root_.mul_assoc]

theorem hv_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), (∀ (k : ℕ) (F F' : Fin n → SecN Xo y.x k) (r : Fin n → S), (∀ b j, (F' b).f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S (r b)) * (F b).f j) → hv Xo c nab y k F' P = (∏ b, r b) * hv Xo c nab y k F P) ∧ (∀ (k : ℕ) (F : Fin n → SecN Xo y.x k) (s : c.F), hv Xo c nab y k F (MvPolynomial.C s * P) = algebraMap c.F S s * hv Xo c nab y k F P) ∧ ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) = hv Xo c nab y (N ^ 2) (fun b => sqN Xo N (F b)) P := by
  intro E _ _ _ H Dw l Xo c _ _ nab hnab S _ _ y n P
  refine ⟨?_, ?_, ?_⟩
  · intro k F F' r hF
    unfold hv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have key : ∀ b, nab y (k : ℤ) (F' b) (colOf m b) = r b * nab y (k : ℤ) (F b) (colOf m b) :=
      fun b => nab_smul_secN Xo c nab hnab y k (F b) (F' b) (r b) (hF b) _
    simp only [key, Finset.prod_mul_distrib]
    ring
  · intro k F s
    unfold hv
    exact sum_support_C_mul P s _
  · intro N F
    unfold hv sqN
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1

end GlobalTheory.PlaceInt
end
end

