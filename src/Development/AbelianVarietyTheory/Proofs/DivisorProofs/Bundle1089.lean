module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralIndicatorEqLatticeCount
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.LatTransfer

open GlobalTheory.UnitLemma

theorem avg_of_const {H : Type} [Group H] (u : H → ℂ) (c : ℂ) (hu : ∀ h, u h = c) : avg u = c := by
  have hs : rStab u = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro k x
    rw [hu, hu]
  have hi : (rStab u).index = 1 := by rw [hs, Subgroup.index_top]
  have hc : Nat.card (H ⧸ rStab u) = 1 := hi
  obtain ⟨x0, hx0⟩ := Nat.card_eq_one_iff_exists.1 hc
  unfold avg
  rw [hi, finsum_eq_single _ x0 (fun y hy => absurd (hx0 y) hy), hu]
  simp

theorem mulLat_eq_self_iff {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (u : Aˣ)
    (L : Submodule O A) : mulLat O (u : A) L = L ↔ u ∈ stabLat O L := by
  constructor
  · intro h
    show ∀ y, y ∈ L ↔ (u : A) * y ∈ L
    intro y
    have := Orbit.mem_mulLat u L ((u : A) * y)
    rw [h, Units.inv_mul_cancel_left] at this
    exact this.symm
  · intro hu
    ext y
    rw [Orbit.mem_mulLat]
    have := hu (((u⁻¹ : Aˣ) : A) * y)
    rw [Units.mul_inv_cancel_left] at this
    exact this

theorem mulLat_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (s t : Aˣ)
    (L : Submodule O A) : mulLat O ((s * t : Aˣ) : A) L = mulLat O (s : A) (mulLat O (t : A) L) := by
  ext y
  rw [Orbit.mem_mulLat, Orbit.mem_mulLat, Orbit.mem_mulLat, _root_.mul_inv_rev, Units.val_mul, mul_assoc]

theorem cast_finsum {α : Type*} (u : α → ℚ) : ((∑ᶠ a, u a : ℚ) : ℂ) = ∑ᶠ a, ((u a : ℚ) : ℂ) := by
  by_cases h : (Function.support u).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have e : Function.support (fun a => ((u a : ℚ) : ℂ)) = Function.support u :=
      Function.support_comp_eq (fun r : ℚ => (r : ℂ)) (fun {x} => Rat.cast_eq_zero) u
    have h' : ¬ (Function.support fun a => ((u a : ℚ) : ℂ)).Finite := by rw [e]; exact h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

theorem twCent_left {G : Type} [Group G] (θ : G →* G) (δ : G) {t : G} (ht : t ∈ twCent θ δ) (k y : G) :
    (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by
  have h : t * δ = δ * θ t := ht
  have h2 : t⁻¹ * δ * θ t = δ := by rw [mul_assoc, ← h]; group
  calc (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * (t⁻¹ * δ * θ t) * θ y) * θ k := by
        simp only [map_mul]; group
    _ = _ := by rw [h2]

theorem twOrb_eq_N : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (Kg : Subgroup G) (δ : G) (f : G → ℂ) (φ : twCent θ δ ≃* B.T) (Λ : G → Submodule K.O B.A), (∀ k ∈ Kg, ∀ y, f (k⁻¹ * y * θ k) = f y) → (∀ y, f y = 0 ∨ f y = 1) → (∀ t : twCent θ δ, ((t : G) ∈ cptPart (twCent θ δ) ↔ (((φ t : B.T) : B.Aˣ)) ∈ GlobalTheory.UnitLemma.intUnits K.O B.A)) → (∀ q q' : G, Λ q = Λ q' ↔ q⁻¹ * q' ∈ Kg) → (∀ (t : twCent θ δ) (q : G), Λ ((t : G) * q) = GlobalTheory.UnitLemma.mulLat K.O ((((φ t : B.T) : B.Aˣ)) : B.A) (Λ q)) → (∀ q, Λ q ∈ B.X x ↔ f (q⁻¹ * δ * θ q) = 1) → (∀ L ∈ B.X x, ∃ q, Λ q = L) → twOrb θ Kg δ f = ((B.N x : ℚ) : ℂ) := by
  intro K B x G _ _ θ Kg δ f φ Λ hf h01 hcpt hΛK hΛT hΛX hsurj

  have havg : ∀ q : G, avg (fun k : Kg => f ((q * k)⁻¹ * δ * θ (q * k))) = f (q⁻¹ * δ * θ q) := by
    intro q
    refine avg_of_const _ _ fun k => ?_
    rw [← hf k k.2 (q⁻¹ * δ * θ q)]
    congr 1
    simp only [map_mul]
    group

  let ψ : twCent θ δ →* B.Aˣ := B.T.subtype.comp φ.toMonoidHom
  have hψ : ∀ t, ψ t = ((φ t : B.T) : B.Aˣ) := fun t => rfl
  have hle : cptPart (twCent θ δ) ≤ twCent θ δ := by
    unfold cptPart
    rw [Subgroup.closure_le]
    exact fun t ht => ht.1
  have hidx : ∀ q : G, (twCent θ δ ⊓ Kg.map (MulAut.conj q).toMonoidHom).relIndex (cptPart (twCent θ δ)) =
      (stabLat K.O (Λ q) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) := by
    intro q
    rw [← Subgroup.relIndex_subgroupOf hle]
    have e1 : (twCent θ δ ⊓ Kg.map (MulAut.conj q).toMonoidHom).subgroupOf (twCent θ δ) =
        (stabLat K.O (Λ q) ⊓ B.T).comap ψ := by
      ext t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf, hψ]
      simp only [t.2, (φ t).2, true_and, and_true]
      rw [← mulLat_eq_self_iff, ← hΛT, eq_comm, hΛK, Subgroup.mem_map]
      constructor
      · rintro ⟨k, hk, hkt⟩
        have : (t : G) = q * k * q⁻¹ := by rw [← hkt]; rfl
        rw [this]
        simpa [mul_assoc] using hk
      · intro h
        refine ⟨q⁻¹ * (t * q), h, ?_⟩
        show q * (q⁻¹ * (t * q)) * q⁻¹ = t
        group
    have e2 : (cptPart (twCent θ δ)).subgroupOf (twCent θ δ) = (intUnits K.O B.A ⊓ B.T).comap ψ := by
      ext t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf, hψ, hcpt t]
      simp only [(φ t).2, and_true]
    rw [e1, e2, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self]
    intro y hy
    exact ⟨φ.symm ⟨y, hy.2⟩, by rw [hψ]; simp⟩

  have hdc : ∀ t ∈ twCent θ δ, ∀ k ∈ Kg, ∀ q : G, f ((t * q * k)⁻¹ * δ * θ (t * q * k)) = f (q⁻¹ * δ * θ q) := by
    intro t ht k hk q
    rw [twCent_left θ δ ht k q, hf k hk]
  let r : B.X x → B.X x → Prop := fun L M => ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) L
  have hr : Equivalence r := by
    refine ⟨fun L => ⟨1, B.T.one_mem, ((mulLat_eq_self_iff 1 L.1).2 (stabLat K.O L.1).one_mem).symm⟩, ?_, ?_⟩
    · rintro L M ⟨t, ht, h⟩
      refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
      rw [h, ← mulLat_mul, inv_mul_cancel]
      exact ((mulLat_eq_self_iff 1 L.1).2 (stabLat K.O L.1).one_mem).symm
    · rintro L M N ⟨t, ht, h⟩ ⟨s, hs, h'⟩
      exact ⟨s * t, B.T.mul_mem hs ht, by rw [h', h, mulLat_mul]⟩
  let S := {d : DoubleCoset.Quotient (twCent θ δ : Set G) (Kg : Set G) //
    f ((Quotient.out d)⁻¹ * δ * θ (Quotient.out d)) = 1}
  let g : S → Orb K.O B.T (B.X x) := fun d => Quot.mk r ⟨Λ (Quotient.out d.1), (hΛX _).2 d.2⟩
  have hg_surj : Function.Surjective g := by
    intro o
    induction o using Quot.ind with
    | mk L =>
      obtain ⟨q, hq⟩ := hsurj L.1 L.2
      obtain ⟨t, ht, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent θ δ) Kg q
      have hf1 : f ((Quotient.out (DoubleCoset.mk (twCent θ δ) Kg q))⁻¹ * δ *
          θ (Quotient.out (DoubleCoset.mk (twCent θ δ) Kg q))) = 1 := by
        rw [hout, hdc t ht k hk q]
        exact (hΛX q).1 (hq ▸ L.2)
      refine ⟨⟨DoubleCoset.mk (twCent θ δ) Kg q, hf1⟩, ?_⟩
      refine (Quot.sound ?_).symm
      refine ⟨((φ ⟨t, ht⟩ : B.T) : B.Aˣ), (φ ⟨t, ht⟩).2, ?_⟩
      show Λ (Quotient.out (DoubleCoset.mk (twCent θ δ) Kg q)) = _
      rw [hout, ← hq, ← hΛT ⟨t, ht⟩ q]
      refine ((hΛK _ _).2 ?_).symm
      simpa [mul_assoc] using hk
  have hg_inj : Function.Injective g := by
    rintro ⟨d1, h1⟩ ⟨d2, h2⟩ h
    obtain ⟨s, hs, hs'⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact h)
    apply Subtype.ext
    let t : twCent θ δ := φ.symm ⟨s, hs⟩
    have hts : ((φ t : B.T) : B.Aˣ) = s := by simp [t]
    have h3 : Λ ((t : G) * Quotient.out d1) = Λ (Quotient.out d2) := by
      rw [hΛT, hts]
      exact hs'.symm
    have := (@DoubleCoset.eq _ _ (twCent θ δ) Kg (Quotient.out d1) (Quotient.out d2)).2
      ⟨t, t.2, (t * Quotient.out d1)⁻¹ * Quotient.out d2, (hΛK _ _).1 h3, by group⟩
    rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at this
  let e := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  have hN : ((B.N x : ℚ) : ℂ) = ∑ᶠ o : Orb K.O B.T (B.X x), ((Orbit.orbWt B.T (B.X x) o : ℚ) : ℂ) := by
    unfold InvAlg.N
    rw [Orbit.orbSum_eq, cast_finsum]
  rw [hN, ← finsum_comp_equiv e]
  have hw : ∀ s : S, ((Orbit.orbWt B.T (B.X x) (e s) : ℚ) : ℂ) =
      (((stabLat K.O (Λ (Quotient.out s.1)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ) := by
    intro s
    exact Rat.cast_natCast _
  rw [finsum_congr hw]
  unfold twOrb
  have hsub : (∑ᶠ s : S, (((stabLat K.O (Λ (Quotient.out s.1)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) =
      ∑ᶠ (d : DoubleCoset.Quotient (twCent θ δ : Set G) (Kg : Set G))
        (_ : f ((Quotient.out d)⁻¹ * δ * θ (Quotient.out d)) = 1),
        (((stabLat K.O (Λ (Quotient.out d)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ) :=
    finsum_subtype_eq_finsum_cond (f := fun d : DoubleCoset.Quotient (twCent θ δ : Set G) (Kg : Set G) =>
      (((stabLat K.O (Λ (Quotient.out d)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) _
  rw [hsub]
  refine finsum_congr fun d => ?_
  rw [havg, hidx, finsum_eq_if]
  rcases h01 ((Quotient.out d)⁻¹ * δ * θ (Quotient.out d)) with h | h
  · rw [h, mul_zero, if_neg (by norm_num)]
  · rw [h, mul_one, if_pos rfl]

end GlobalTheory.LatTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
section
open Filter GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwOrbGood

theorem avg_const {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have h : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold GlobalTheory.BCT.avg
  rw [h, Subgroup.index_top]
  have : (∑ᶠ q : H ⧸ (⊤ : Subgroup H), (fun _ : H => c) q.out) = c := by
    rw [finsum_eq_single (fun q : H ⧸ (⊤ : Subgroup H) => (fun _ : H => c) q.out) (QuotientGroup.mk 1)
      (fun q hq => absurd (by induction q using QuotientGroup.induction_on with | H a => exact QuotientGroup.eq.2 (Subgroup.mem_top _)) hq)]
  rw [this]; simp

theorem summand_goodplace : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (KH : Subgroup H) (δ : H), δ ∈ KH → cptPart (twCent (MonoidHom.id H) δ) ≤ KH → (∀ g : H, g⁻¹ * δ * g ∈ KH → ∃ t ∈ twCent (MonoidHom.id H) δ, t⁻¹ * g ∈ KH) → ∀ x : H, GlobalTheory.TwOrbConj.summand (MonoidHom.id H) KH δ ((KH : Set H).indicator 1) x = if ∃ t ∈ twCent (MonoidHom.id H) δ, ∃ k ∈ KH, x = t * k then 1 else 0 := by
  intro H _ _ _ KH δ hδ hc hg x
  split_ifs with hx
  · obtain ⟨t, ht, k, hk, rfl⟩ := hx
    have e : t * k = t * 1 * k := by group
    rw [e, GlobalTheory.TwOrbConj.summand_rep _ _ _ _ _ ht hk]
    unfold GlobalTheory.TwOrbConj.summand
    have hmap : KH.map (MulAut.conj (1 : H)).toMonoidHom = KH := GlobalTheory.TwOrbConj.map_conj_self KH KH.one_mem
    have hcT : cptPart (twCent (MonoidHom.id H) δ) ≤ twCent (MonoidHom.id H) δ := by
      unfold GlobalTheory.BCT.cptPart
      rw [Subgroup.closure_le]
      intro y hy; exact hy.1
    have hrel : (twCent (MonoidHom.id H) δ ⊓ KH.map (MulAut.conj (1 : H)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id H) δ)) = 1 := by
      rw [hmap, Subgroup.relIndex_eq_one]
      exact le_inf hcT hc
    have hfun : (fun k : KH => (KH : Set H).indicator (1 : H → ℂ) ((1 * (k : H))⁻¹ * δ * (MonoidHom.id H) (1 * (k : H))))
        = fun _ => 1 := by
      funext k
      rw [Set.indicator_of_mem]
      · rfl
      · simp only [one_mul, MonoidHom.id_apply]
        exact KH.mul_mem (KH.mul_mem (KH.inv_mem k.2) hδ) k.2
    rw [hrel, hfun, avg_const]; simp
  · unfold GlobalTheory.TwOrbConj.summand
    have hfun : (fun k : KH => (KH : Set H).indicator (1 : H → ℂ) ((x * (k : H))⁻¹ * δ * (MonoidHom.id H) (x * (k : H))))
        = fun _ => 0 := by
      funext k
      rw [Set.indicator_of_notMem]
      intro hm
      simp only [MonoidHom.id_apply] at hm
      obtain ⟨t, ht, htk⟩ := hg (x * k) hm
      apply hx
      refine ⟨t, ht, t⁻¹ * (x * k) * (k : H)⁻¹, KH.mul_mem htk (KH.inv_mem k.2), by group⟩
    rw [hfun, avg_const]; simp

end GlobalTheory.TwOrbGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitary
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwTrUnit

theorem trace_eq_zero_of_finrank_eq_zero (W : Type) [AddCommGroup W] [Module ℂ W] (h : Module.finrank ℂ W = 0)
    (L : W →ₗ[ℂ] W) : LinearMap.trace ℂ W L = 0 := by
  by_cases hW : Module.Finite ℂ W
  · haveI : Subsingleton W := Module.finrank_zero_iff.1 h
    rw [show L = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
  · unfold LinearMap.trace
    rw [dite_eq_right]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hW (Module.Finite.of_basis b)

theorem isHecke_indicator {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G}
    (hK : IsCompact (K : Set G)) (ho : IsOpen (K' : Set G)) (hle : K' ≤ K) :
    IsHecke K' ((K' : Set G).indicator (1 : G → ℂ)) := by
  have hcl : IsClosed (K' : Set G) := K'.isClosed_of_isOpen ho
  have hc : IsCompact (K' : Set G) := hK.of_isClosed_subset hcl hle
  refine ⟨HasCompactSupport.intro' hc hcl fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩
  · have : k * x ∈ (K' : Set G) ↔ x ∈ (K' : Set G) := K'.mul_mem_cancel_left hk
    simp only [Set.indicator_apply, this, Pi.one_apply]
  · have : x * k ∈ (K' : Set G) ↔ x ∈ (K' : Set G) := K'.mul_mem_cancel_right hk
    simp only [Set.indicator_apply, this, Pi.one_apply]

theorem twTr_indicator {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) : twTr ρ K K' ((K' : Set G).indicator 1) LinearMap.id =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed ρ K') : ℂ) := by
  obtain ⟨x₀, hx₀, hL⟩ := GlobalTheory.TwTrLin.levOp_unit ρ K K'
  have hfx : ∀ v ∈ fixed ρ K', ρ x₀ v = v := fun v hv => (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' v).1 hv x₀ hx₀
  have hm : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K' := by
    intro v hv
    rw [hL, LinearMap.smul_apply, hfx v hv]
    exact Submodule.smul_mem _ _ hv
  rw [GlobalTheory.TwTrLin.twTr_eq _ _ _ _ _ hm]
  have hr : (levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id).restrict hm =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext x
    simp [LinearMap.restrict_apply, hL, hfx x.1 x.2]
  rw [hr, map_smul, GlobalTheory.TwTrLin.trace_id_eq_finrank, smul_eq_mul]

theorem twTr_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id (UL n w)) (KL n w) K' → ∀ σ : SmIrr (UL n w), IsHecke K' ((K' : Set (UL n w)).indicator 1) ∧ K'.relIndex (KL n w) ≠ 0 ∧ twTr σ.ρ (KL n w) K' ((K' : Set (UL n w)).indicator 1) LinearMap.id = ((K'.relIndex (KL n w) : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed σ.ρ K') : ℂ) ∧ (Module.finrank ℂ (fixed σ.ρ K') = 0 → ∀ g, twTr σ.ρ (KL n w) K' g LinearMap.id = 0) := by
  intro E _ _ _ n w K' hlev σ
  have hKc := GlobalTheory.LocFinU.isCompact_KL n w
  refine ⟨isHecke_indicator hKc hlev.1 hlev.2.1, GlobalTheory.TwTrLin.relIndex_ne_zero_of_isOpen hKc hlev.1,
    twTr_indicator _ _ _, fun h g => ?_⟩
  unfold twTr
  split_ifs with hm
  · exact trace_eq_zero_of_finrank_eq_zero _ h _
  · rfl

end GlobalTheory.TwTrUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAevalKernelsOrthogonalOfCoprime
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryOrth

theorem aeval_mulVec_mem_of_stable {K : Type} [Field K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) (hW : ∀ z ∈ W, γ *ᵥ z ∈ W) (p : K[X]) :
    ∀ z ∈ W, aeval γ p *ᵥ z ∈ W := by
  induction p using Polynomial.induction_on with
  | C c =>
    intro z hz
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem _ hz
  | add p q hp hq =>
    intro z hz
    rw [map_add (f := _), Matrix.add_mulVec]
    exact W.add_mem (hp z hz) (hq z hz)
  | monomial m c h =>
    intro z hz
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec]
    exact h _ (hW z hz)

theorem form_mulVec_mulVec {K : Type} [Field K] (σ : K →+* K) {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hγ : (γ.map σ)ᵀ * γ = 1) (x z : Fin n → K) :
    ∑ k, σ ((γ *ᵥ x) k) * (γ *ᵥ z) k = ∑ k, σ (x k) * z k := by
  have h1 : (fun k => σ ((γ *ᵥ x) k)) = (γ.map σ) *ᵥ (fun k => σ (x k)) := by
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  have h2 : ∑ k, σ ((γ *ᵥ x) k) * (γ *ᵥ z) k = (fun k => σ ((γ *ᵥ x) k)) ⬝ᵥ (γ *ᵥ z) := rfl
  rw [h2, h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hγ,
    Matrix.one_mulVec]
  rfl

theorem ker_orthogonal_of_coprime :
    ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), (γ.map σ)ᵀ * γ = 1 →
    ∀ (q₁ q₂ a b : K[X]), a * q₁ + b * q₂ = 1 → aeval γ (q₁ * q₂) = 0 →
    ∀ (V : Submodule K (Fin n → K)), (∀ x, x ∈ V ↔ aeval γ q₁ *ᵥ x = 0) →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (bs : Module.Basis ι K V),
    (Matrix.of fun i j => ∑ k, σ ((bs i : Fin n → K) k) * (bs j : Fin n → K) k).det ≠ 0 →
    ∀ x ∈ V, ∀ y : Fin n → K, aeval γ q₂ *ᵥ y = 0 → ∑ k, σ (x k) * y k = 0 := by
  intro K _ σ n γ hγ q₁ q₂ a b hab _ V hV ι _ _ bs hG x hx y hy
  have hcomm : ∀ p q : K[X], aeval γ p * aeval γ q = aeval γ q * aeval γ p := by
    intro p q
    rw [← map_mul, ← map_mul, mul_comm]
  have hVst : ∀ z ∈ V, γ *ᵥ z ∈ V := by
    intro z hz
    rw [hV] at hz ⊢
    have := hcomm q₁ X
    rw [aeval_X] at this
    rw [Matrix.mulVec_mulVec, this, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  have hsurj : ∀ z ∈ V, ∃ z' ∈ V, γ *ᵥ z' = z := by
    intro z hz
    let f : V →ₗ[K] V := (Matrix.mulVecLin γ).restrict (p := V) (q := V) hVst
    have hf : Function.Injective f := by
      intro u v huv
      have h1 : γ *ᵥ (u : Fin n → K) = γ *ᵥ (v : Fin n → K) := congrArg Subtype.val huv
      have h2 := congrArg (fun t => (γ.map σ)ᵀ *ᵥ t) h1
      simp only [Matrix.mulVec_mulVec, hγ, Matrix.one_mulVec] at h2
      exact Subtype.ext h2
    obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hf) ⟨z, hz⟩
    exact ⟨u, u.2, congrArg Subtype.val hu⟩
  let W : Submodule K (Fin n → K) :=
    { carrier := {z | ∀ x ∈ V, ∑ k, σ (x k) * z k = 0}
      add_mem' := by
        intro u v hu hv x hx
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hu x hx, hv x hx, add_zero]
      zero_mem' := by
        intro x _
        simp
      smul_mem' := by
        intro c u hu x hx
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, hu x hx,
          mul_zero] }
  have hWmem : ∀ z, z ∈ W ↔ ∀ x ∈ V, ∑ k, σ (x k) * z k = 0 := fun z => Iff.rfl
  have hWst : ∀ z ∈ W, γ *ᵥ z ∈ W := by
    intro z hz
    rw [hWmem] at hz ⊢
    intro u hu
    obtain ⟨u', hu', rfl⟩ := hsurj u hu
    rw [form_mulVec_mulVec σ γ hγ]
    exact hz u' hu'
  set G : Matrix ι ι K :=
    Matrix.of fun i j => ∑ k, σ ((bs i : Fin n → K) k) * (bs j : Fin n → K) k with hGdef
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hGc : ∀ (c : ι → K) (i : ι), (G *ᵥ c) i =
      ∑ k, σ ((bs i : Fin n → K) k) * ((∑ j, c j • bs j : V) : Fin n → K) k := by
    intro c i
    simp only [hGdef, Matrix.mulVec, dotProduct, Matrix.of_apply, Submodule.coe_sum,
      Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hWbs : ∀ z : Fin n → K, (∀ i, ∑ k, σ ((bs i : Fin n → K) k) * z k = 0) → z ∈ W := by
    intro z hz
    rw [hWmem]
    intro u hu
    have h1 : u = ((∑ j, bs.repr ⟨u, hu⟩ j • bs j : V) : Fin n → K) := by
      rw [bs.sum_repr]
    rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum, hz j, mul_zero]
  have hVW : ∀ z ∈ V, z ∈ W → z = 0 := by
    intro z hz hzW
    have h0 : G *ᵥ (bs.repr ⟨z, hz⟩ : ι → K) = 0 := by
      funext i
      rw [hGc, bs.sum_repr]
      exact (hWmem z).mp hzW _ (bs i).2
    have h1 : (bs.repr ⟨z, hz⟩ : ι → K) = 0 := Matrix.eq_zero_of_mulVec_eq_zero hG h0
    have h2 : bs.repr ⟨z, hz⟩ = 0 := by
      ext i
      exact congrFun h1 i
    have h3 : (⟨z, hz⟩ : V) = 0 := bs.repr.map_eq_zero_iff.mp h2
    exact congrArg Subtype.val h3
  let c : ι → K := G⁻¹ *ᵥ (fun i => ∑ k, σ ((bs i : Fin n → K) k) * y k)
  let y₁ : V := ∑ j, c j • bs j
  have hy₀ : y - (y₁ : Fin n → K) ∈ W := by
    apply hWbs
    intro i
    have h1 := hGc c i
    have h2 : G *ᵥ c = fun i => ∑ k, σ ((bs i : Fin n → K) k) * y k := by
      simp only [c]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec]
    rw [h2] at h1
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h1
  have hq₂ : aeval γ q₂ *ᵥ (y₁ : Fin n → K) = 0 := by
    apply hVW _ (aeval_mulVec_mem_of_stable γ V hVst q₂ _ y₁.2)
    have h1 := W.neg_mem (aeval_mulVec_mem_of_stable γ W hWst q₂ _ hy₀)
    rwa [Matrix.mulVec_sub, hy, zero_sub, neg_neg] at h1
  have hq₁ : aeval γ q₁ *ᵥ (y₁ : Fin n → K) = 0 := (hV _).mp y₁.2
  have hy₁ : (y₁ : Fin n → K) = 0 := by
    have h1 : aeval γ (a * q₁ + b * q₂) *ᵥ (y₁ : Fin n → K) = y₁ := by
      rw [hab, map_one, Matrix.one_mulVec]
    rw [← h1, map_add (f := _), map_mul, map_mul, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hq₁, hq₂, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  rw [hy₁, sub_zero] at hy₀
  exact (hWmem y).mp hy₀ x hx

end GlobalTheory.UnitaryOrth
end

