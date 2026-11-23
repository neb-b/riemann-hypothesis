module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Formalism.UnipotentAdelicQuotients.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare

noncomputable section

namespace GlobalTheory.VacUnique

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem apply_real_add (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {u : WO S T} (hu : u.map (infPart D) = 0)
    {f : WO S T → ℂ} {ε : ℂ} (hf : heisO ψ S T u f = ε • f) (z : RW T S) :
    f (iotaW σ T S z + u) = ε * f (iotaW σ T S z) := by
  have e : ψ (symplOH S T (iotaW σ T S z) u) * f (iotaW σ T S z + u) = ε * f (iotaW σ T S z) := congrFun hf _
  rw [_root_.GlobalTheory.OrientedChar.char_symplOH D θ ψ h.inf hψ S T _ _ (Or.inl (h.real_iota T S z)), piW_of_inf θ hu, LinearMap.map_zero] at e
  simpa using e

theorem exists_decomp (h : Chart θ σ) {Λ : AddSubgroup (WO S T)}
    (h2 : ∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0)
    (w : WO S T) : ∃ γ z, ∃ u ∈ Λ, w = ratW T S γ + (iotaW σ T S z + u) := by
  have h0 : (w - iotaW σ T S (piW θ T S w) : WO S T).map (infPart D) = 0 := by
    have hp : piW θ T S (w - iotaW σ T S (piW θ T S w)) = 0 := by
      rw [AddMonoidHom.map_sub, h.pi_iota, sub_self]
    funext i j
    exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  obtain ⟨_, ⟨γ, rfl⟩, u, hu, hr⟩ := h2 _ h0
  refine ⟨γ, piW θ T S w + piW θ T S (w - iotaW σ T S (piW θ T S w) - ratW T S γ - u), u, hu, ?_⟩
  rw [AddMonoidHom.map_add (f := _), h.iota_pi (x := w - iotaW σ T S (piW θ T S w) - ratW T S γ - u) hr]
  abel

theorem apply_add_infRat (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {ε : ℂ} (he : heisO ψ S T (finRat S T (-v)) f = ε • f) (z : RW T S) :
    f (iotaW σ T S (z + infRat S T v)) =
      (ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε) *
        Complex.exp (-(Real.pi * Complex.I) * (-omO S T (infRat S T v) z : ℝ)) * f (iotaW σ T S z) := by
  have e : iotaW σ T S (z + infRat S T v) = ratW T S v + (iotaW σ T S z + finRat S T (-v)) := by
    rw [ratW_eq h, AddMonoidHom.map_add (f := _), AddMonoidHom.map_neg]
    abel
  have e2 : symplOH S T (ratW T S v) (iotaW σ T S z + finRat S T (-v)) =
      symplOH S T (ratW T S v) (iotaW σ T S z) + symplOH S T (ratW T S v) (finRat S T (-v)) := by
    unfold symplOH
    rw [(_root_.GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1, mul_add]
  rw [e, hf.quasi, apply_real_add h hψ (finRat_inf S T _) he, e2, neg_add, AddChar.map_add_eq_mul,
    AddChar.map_neg_eq_inv ψ (symplOH S T (ratW T S v) (iotaW σ T S z)),
    _root_.GlobalTheory.OrientedChar.char_symplOH D θ ψ h.inf hψ S T _ _ (Or.inr (h.real_iota T S z)), piW_ratW h.inf, h.pi_iota, ← Complex.exp_neg]
  push_cast
  ring_nf

theorem infRat_injective (S T : HSp D) : Function.Injective (infRat S T) := by
  intro x y e
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    exact ⟨((GlobalTheory.CMTypePlaces.places_bijective D).2 w).choose⟩
  funext i j
  exact (tauE D τ).injective (congrFun (congrFun (congrFun e τ) i) j)

private theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
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


theorem vacUniqueO : ∀ D : D7, VacUniqueO D := by
  classical
  intro D ψ θ hψ hθ S T sS sT _ _ hS hT ΛS ΛT hΛS hΛT f f' hf hf'
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT
    (selfDual_isFullLattice S ΛS hΛS) (selfDual_isFullLattice T ΛT hΛT)
  have hlat := hf.2.lat
  have hlat' := hf'.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat

  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have n2 : nrm2 p.1 p.2 f' = 1 := hf'.2.norm.2 p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := _root_.GlobalTheory.RealSymplForm.form_alt_inv_def D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := _root_.GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := _root_.GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ h ψ hψ S T sS sT f' hf'.2.theta hf'.2.fock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := _root_.GlobalTheory.VacuumLine.not_linearIndependent (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (_root_.GlobalTheory.RatSelfDual.finRat_mem_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hf'.2.theta hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  have e := det f f' a hf.2.theta hf'.2.theta hlat hlat' fun z => (congrFun ha z).symm
  refine ⟨a, ?_, e⟩
  have n3 : nrm2 p.1 p.2 (a • f) = ‖a‖ ^ 2 * nrm2 p.1 p.2 f := by
    simp only [nrm2, Pi.smul_apply, norm_smul, mul_pow]
    exact integral_const_mul _ _
  rw [e, n3, n1, mul_one] at n2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).1 n2

end GlobalTheory.VacUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteHolds
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem classNumberFinite_holds : HeckeCharacterZeroLocus.ClassNumberFinite := by
  classical
  intro F _ _ n S hS U hUo _
  obtain ⟨T₀, hT₀, hx⟩ := _root_.GlobalTheory.ClassFin.classFinite_integralLevel F n S (fun B _ _ =>
    ⟨(hS B).1, fun g h hg hh => (hS B).2.1 g hg h hh, fun g hg => (hS B).2.2 g hg⟩)
  have hK := _root_.GlobalTheory.IntegralPointsCompact.isCompact_integral_points F n S (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))
    (fun g => Iff.rfl)
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.compact_meets_finitely_many_leftCosets_open _ U _ hUo hK
  refine ⟨Finset.image₂ (fun (s : T₀) (t : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) =>
    (⟨s.1, hT₀ s.1 s.2⟩ : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) * t) T₀.attach T₁, ?_⟩
  intro x
  obtain ⟨γ, hγ, s, hs, k, hk, hki, hxe⟩ := hx x.1 x.2
  obtain ⟨t, ht, u, hu, hke⟩ := hT₁ ⟨k, hk⟩ hki
  refine ⟨γ, hγ, _, Finset.mem_image₂_of_mem (Finset.mem_attach T₀ ⟨s, hs⟩) ht, u, hu, ?_⟩
  have hke' : k = t.1 * u.1 := congrArg Subtype.val hke
  rw [hxe, hke']
  simp only [Subgroup.coe_mul, mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SemiChar

theorem exists_abstract {G R : Type} [AddCommGroup G] [AddCommGroup R] (ψ : AddChar R ℂ) (hψ : ∀ r, ‖ψ r‖ ≤ 1)
    (B : G → G → R) (hl : ∀ x y z, B (x + y) z = B x z + B y z) (hr : ∀ x y z, B x (y + z) = B x y + B x z)
    (ha : ∀ x, B x x = 0) (L : AddSubgroup G) (K : G → Prop) (K0 : K 0) (Ksub : ∀ x y, K x → K y → K (x - y))
    (hKL : ∀ l ∈ L, K l → l = 0) (hB : ∀ x, K x → ∀ l ∈ L, B x l = 0)
    (h2 : ∀ a ∈ L, ∀ u ∈ L, ψ (B a u + B a u) = 1)
    (p q : G → G) (padd : ∀ x y, p (x + y) = p x + p y) (pq : ∀ x, p x + q x = x)
    (adj : ∀ x y, B (p x) y = B x (q y)) (pL : ∀ l ∈ L, p l ∈ L) :
    ∃ χ : G → ℂ, (∀ x, (¬ ∃ l ∈ L, K (x - l)) → χ x = 0) ∧ (∀ x, ‖χ x‖ ≤ 1) ∧ χ 0 = 1 ∧
      (∀ x y, K y → χ (x + y) = χ x) ∧ (∀ u ∈ L, ∀ x, ψ (B x (2 • u)) * χ (x + 2 • u) = χ x) ∧
      ∀ u ∈ L, B (p u) u = 0 → ∀ x, ψ (B x u) * χ (x + u) = χ x := by
  classical
  have Kadd : ∀ x y, K x → K y → K (x + y) := fun x y hx hy => by
    have := Ksub x (0 - y) hx (Ksub 0 y K0 hy)
    rwa [zero_sub, sub_neg_eq_add] at this
  have skew : ∀ x y, B x y + B y x = 0 := fun x y => by
    have := ha (x + y)
    rwa [hl, hr, hr, ha, ha, zero_add, add_zero] at this
  let χ : G → ℂ := fun x => if h : ∃ l ∈ L, K (x - l) then ψ (B (p h.choose) h.choose) else 0
  have hn : ∀ x, (¬ ∃ l ∈ L, K (x - l)) → χ x = 0 := fun x h => dif_neg h
  have hy : ∀ x, ∀ l ∈ L, K (x - l) → χ x = ψ (B (p l) l) := fun x l hl' hk => by
    have h : ∃ l ∈ L, K (x - l) := ⟨l, hl', hk⟩
    have e : h.choose = l := by
      have h1 := Ksub _ _ hk h.choose_spec.2
      rw [sub_sub_sub_cancel_left] at h1
      exact sub_eq_zero.1 (hKL _ (L.sub_mem h.choose_spec.1 hl') h1)
    show dite _ _ _ = _
    rw [dite_eq_left h, e]
  have gen : ∀ u ∈ L, (∀ l ∈ L, ψ (B l u) * ψ (B (p (l + u)) (l + u)) = ψ (B (p l) l)) →
      ∀ x, ψ (B x u) * χ (x + u) = χ x := fun u hu H x => by
    by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      have e : B x u = B l u := by
        have := hl (x - l) l u
        rwa [sub_add_cancel, hB _ hk u hu, zero_add] at this
      rw [hy x l hl' hk, hy (x + u) (l + u) (L.add_mem hl' hu) (by rwa [add_sub_add_right_eq_sub]), e, H l hl']
    · rw [hn x h, hn (x + u), mul_zero]
      rintro ⟨l, hl', hk⟩
      exact h ⟨l - u, L.sub_mem hl' hu, by rwa [← sub_add, sub_add_eq_add_sub]⟩
  refine ⟨χ, hn, fun x => ?_, ?_, fun x y hk => ?_, fun u hu => ?_, fun u hu h0 => ?_⟩
  · by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      rw [hy x l hl' hk]; exact hψ _
    · rw [hn x h]; simp
  · rw [hy 0 0 L.zero_mem (by rwa [sub_zero])]
    have : B (p 0) 0 = 0 := by
      have := hr (p 0) 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [this, AddChar.map_zero_eq_one]
  · by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      rw [hy x l hl' hk, hy (x + y) l hl' (by rw [← sub_add_eq_add_sub]; exact Kadd _ _ hk ‹_›)]
    · rw [hn x h, hn (x + y)]
      rintro ⟨l, hl', hk'⟩
      refine h ⟨l, hl', ?_⟩
      have := Ksub _ _ hk' hk
      rwa [show x + y - l - y = x - l by abel] at this
  · refine gen _ (L.nsmul_mem hu 2) fun l hl' => ?_
    have e : B (p (l + 2 • u)) (l + 2 • u) = B (p l) l + (B (p l) u + B (p l) u) +
        (B (p u) (l + 2 • u) + B (p u) (l + 2 • u)) := by
      conv_lhs => rw [padd, hl, hr, two_nsmul, hr, padd, hl]
      rw [two_nsmul]
    rw [e, two_nsmul, hr, h2 l hl' u hu, one_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      h2 _ (pL l hl') u hu, h2 _ (pL u hu) _ (L.add_mem hl' (L.add_mem hu hu)), mul_one, mul_one]
  · refine gen _ hu fun l hl' => ?_
    have e : B l u + B (p (l + u)) (l + u) = B (p l) l + (B (p l) u + B (p l) u) := by
      have e1 : B l u = B (p l) u + B (q l) u := by rw [← hl, pq]
      have e2 := skew u (q l)
      rw [padd, hl, hr, hr, h0, adj u l, e1]
      rw [← sub_eq_zero]
      refine Eq.trans ?_ e2
      abel
    rw [← AddChar.map_add_eq_mul, e, AddChar.map_add_eq_mul, h2 _ (pL l hl') u hu, mul_one]

variable {D : D7}

theorem latO_inf (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : ∀ l ∈ latO S T LS LT P, l.map (infPart D) = 0 := by
  intro l hl
  induction hl using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hw
    funext i j
    exact TensorProduct.zero_tmul _ _
  | zero => funext i j; exact (infPart D).map_zero
  | add x y _ _ hx hy =>
    funext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
    show infPart D (x i j + y i j) = 0
    rw [RingHom.map_add (f := _), h1, h2, add_zero]
  | neg x _ hx =>
    funext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    show infPart D (-x i j) = 0
    rw [RingHom.map_neg, h1, neg_zero]

theorem map_mul_add {m n : ℕ} (a : AE D) (x y : Mx D m n) :
    (x + y).map (fun z => a * z) = x.map (fun z => a * z) + y.map (fun z => a * z) := by
  funext i j; exact mul_add a (x i j) (y i j)

theorem latO_mul_int (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (b : 𝓞 D.host.E) :
    ∀ l ∈ latO S T LS LT P, l.map (fun z => incA D (b : D.host.E) * z) ∈ latO S T LS LT P := by
  intro l hl
  induction hl using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, h1, h2, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, h1, h2, b • a, Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) b ha,
      s, hs, t, ht, ?_⟩
    funext i j
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) * (_ ⊗ₜ[D.host.F] _) = (_ ⊗ₜ[D.host.F] _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    show (b : D.host.E) * _ = (b : D.host.E) * a * _ * _
    ring
  | zero =>
    have : (0 : WO S T).map (fun z => incA D (b : D.host.E) * z) = 0 := by funext i j; exact mul_zero _
    rw [this]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_mul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx =>
    have : (-x).map (fun z => incA D (b : D.host.E) * z) = -x.map (fun z => incA D (b : D.host.E) * z) := by
      funext i j; exact mul_neg _ _
    rw [this]; exact AddSubgroup.neg_mem _ hx

theorem exists_int_add_star (D : D7) : ∃ b : 𝓞 D.host.E, (b : D.host.E) + star (b : D.host.E) = 1 := by
  refine ⟨⟨(1 + D.host.sqrtMinusD) / 2,
    GlobalTheory.NormSum.isIntegral_half_one_add D.host.d D.host.hyp.2.2.2.1 _ (D.host.sqd_sq)⟩, ?_⟩
  have h2 : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  show (1 + D.host.sqrtMinusD) / 2 + star ((1 + D.host.sqrtMinusD) / 2) = 1
  rw [star_div₀, star_add, star_one, h2, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]
  ring

theorem exists_semichar : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), l.map (infPart D) = 0) ∧ ∃ χ : WO S T → ℂ, (∀ x, (¬ ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - l).map (finPart D) = 0) → χ x = 0) ∧ (∀ x, ‖χ x‖ ≤ 1) ∧ χ 0 = 1 ∧ (∀ x y, y.map (finPart D) = 0 → χ (x + y) = χ x) ∧ (∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ∀ x, ψ (symplOH S T x (2 • u)) * χ (x + 2 • u) = χ x) ∧ ∀ e, IsSplitIdem D e → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf e u → ∀ x, ψ (symplOH S T x u) * χ (x + u) = χ x := by
  intro D S T ΛS ΛT ψ hψ hS hT
  have hinf := latO_inf S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True
  refine ⟨hinf, ?_⟩
  obtain ⟨f1, f2, f3, f4, -, -, f7, f8, f9⟩ := _root_.GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have g := (_root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  obtain ⟨b, hb⟩ := exists_int_add_star D
  obtain ⟨χ, c1, c2, c3, c4, c5, c6⟩ := exists_abstract ψ (fun r => (hψ.1.2.1 r).le) (symplOH S T) f1 f2 f3
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (fun x => x.map (finPart D) = 0) (by funext i j; exact (finPart D).map_zero)
    (fun x y hx hy => by
      funext i j
      have h1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
      have h2 : finPart D (y i j) = 0 := congrFun (congrFun hy i) j
      show finPart D (x i j - y i j) = 0
      rw [RingHom.map_sub, h1, h2, sub_zero])
    (fun l hl hk => by
      funext i j
      exact GlobalTheory.FockCompare.RealChart.adele_tensor_ext (l i j) (congrFun (congrFun (hinf l hl) i) j)
        (congrFun (congrFun hk i) j))
    (fun x hx l hl => f9 x l hx (hinf l hl))
    (fun a ha u hu => by rw [f4]; exact (g a (hinf a ha)).1 ha u hu)
    (fun x => x.map fun z => incA D (b : D.host.E) * z) (fun x => x.map fun z => cA D (incA D (b : D.host.E)) * z)
    (map_mul_add _)
    (fun x => by
      funext i j
      show incA D (b : D.host.E) * x i j + incA D (star (b : D.host.E)) * x i j = x i j
      rw [← add_mul, ← RingHom.map_add (f := _), hb, RingHom.map_one, one_mul])
    (f7 _) (latO_mul_int S T _ _ _ b)
  exact ⟨χ, c1, c2, c3, c4, c5, fun e he u hu hh => c6 u hu (f8 e _ u he.2.1 hh)⟩

end GlobalTheory.SemiChar
end

