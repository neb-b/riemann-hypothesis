module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsAlg
section
noncomputable section

namespace SheetDecomposition.ChartAlg

open MvPolynomial Filter Topology

theorem exists_coords {σ : Type} [Fintype σ] {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (L : E →ₗ[ℂ] (σ → ℂ)) (hL : Function.Injective L) :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → σ), Fintype.card κ = Module.finrank ℂ E ∧
      Function.Surjective (fun (x : E) (k : κ) => L x (a k)) := by
  classical
  let f : σ → Module.Dual ℂ E := fun s => (LinearMap.proj s).comp L
  have hproj : Submodule.span ℂ (Set.range fun s : σ => (LinearMap.proj s : (σ → ℂ) →ₗ[ℂ] ℂ)) = ⊤ := by
    refine eq_top_iff.2 fun φ _ => ?_
    have hφ : φ = ∑ s, φ (Pi.single s 1) • (LinearMap.proj s : (σ → ℂ) →ₗ[ℂ] ℂ) := by
      refine LinearMap.pi_ext fun i c => ?_
      have hsc : (Pi.single i c : σ → ℂ) = c • Pi.single i 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      simp [hsc, Pi.single_apply, mul_comm]
    rw [hφ]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  have htop : Submodule.span ℂ (Set.range f) = ⊤ := by
    have hr : Set.range f = L.dualMap '' Set.range fun s : σ => (LinearMap.proj s : (σ → ℂ) →ₗ[ℂ] ℂ) := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, hproj, Submodule.map_top, LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      LinearMap.ker_eq_bot.2 hL, Submodule.dualAnnihilator_bot]
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℂ (Set.range f)
  have : Finite b := hli.finite
  let _ : Fintype b := Fintype.ofFinite b
  have hbtop : Submodule.span ℂ b = ⊤ := hspan.trans htop
  let a : b → σ := fun k => (hb k.2).choose
  have ha : ∀ k : b, f (a k) = k := fun k => (hb k.2).choose_spec
  refine ⟨b, inferInstance, a, ?_, ?_⟩
  · have B := Module.Basis.mk hli (by rw [Subtype.range_coe, hbtop])
    rw [← Module.finrank_eq_card_basis B, Subspace.dual_finrank_eq]
  · let T : E →ₗ[ℂ] (b → ℂ) := LinearMap.pi fun k => (k : Module.Dual ℂ E)
    have hT : ∀ x, T x = fun k => L x (a k) := by
      intro x; funext k
      show (k : Module.Dual ℂ E) x = L x (a k)
      rw [← ha k]; rfl
    have hinj : Function.Injective T := by
      refine (injective_iff_map_eq_zero T).2 fun x hx => ?_
      have h0 : ∀ φ : Module.Dual ℂ E, φ x = 0 := by
        intro φ
        have hφ : φ ∈ Submodule.span ℂ b := hbtop ▸ Submodule.mem_top
        induction hφ using Submodule.span_induction with
        | mem ψ hψ => exact congrFun hx ⟨ψ, hψ⟩
        | zero => rfl
        | add ψ χ _ _ h1 h2 => rw [LinearMap.add_apply, h1, h2, add_zero]
        | smul c ψ _ h => rw [LinearMap.smul_apply, h, smul_zero]
      exact (Module.forall_dual_apply_eq_zero_iff ℂ x).1 h0
    have hsurjT : Function.Surjective T := by
      refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj
      have B := Module.Basis.mk hli (by rw [Subtype.range_coe, hbtop])
      rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_basis B, Subspace.dual_finrank_eq]
    intro y
    obtain ⟨x, hx⟩ := hsurjT y
    exact ⟨x, (hT x).symm.trans hx⟩

theorem eq_zero_of_eventually {κ : Type} [Fintype κ] (q : MvPolynomial κ ℤ) (u : κ → ℂ)
    (h : ∀ᶠ v in 𝓝 u, aeval v q = 0) : q = 0 := by
  classical
  have he : ∀ v, aeval v q = eval v (MvPolynomial.map (Int.castRingHom ℂ) q) := by
    intro v
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def,
      Subsingleton.elim (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]
  have han := AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id ℂ (κ → ℂ))
    (MvPolynomial.map (Int.castRingHom ℂ) q)
  have hz : ∀ v, eval v (MvPolynomial.map (Int.castRingHom ℂ) q) = 0 := by
    intro v
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ u)
      (h.mono fun w hw => by
        show eval w (MvPolynomial.map (Int.castRingHom ℂ) q) = 0
        rw [← he]; exact hw) (Set.mem_univ v)
    simpa using this
  have hp0 : MvPolynomial.map (Int.castRingHom ℂ) q = MvPolynomial.map (Int.castRingHom ℂ) 0 :=
    MvPolynomial.funext fun v => by rw [hz v, map_zero, map_zero]
  exact MvPolynomial.map_injective _ Int.cast_injective hp0

theorem not_eventually_zero {σ : Type} [Fintype σ] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : Algebra.trdeg ℤ (MvPolynomial σ ℤ ⧸ P) ≤ (Module.finrank ℂ E : Cardinal))
    (Γ : E → σ → ℂ) (w₀ : E) (L : E →L[ℂ] (σ → ℂ)) (hΓ : HasStrictFDerivAt Γ L w₀) (hL : Function.Injective L)
    (hv : ∀ f ∈ P, ∀ᶠ w in 𝓝 w₀, aeval (Γ w) f = 0) (g : MvPolynomial σ ℤ) (hg : g ∉ P) :
    ¬ ∀ᶠ w in 𝓝 w₀, aeval (Γ w) g = 0 := by
  classical
  intro hg0
  obtain ⟨κ, _, a, hcard, hsurj⟩ := exists_coords L.toLinearMap hL
  let Pa : (σ → ℂ) →L[ℂ] (κ → ℂ) := ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (a k)
  have hφ : HasStrictFDerivAt (fun w => fun k => Γ w (a k)) (Pa.comp L) w₀ :=
    Pa.hasStrictFDerivAt.comp w₀ hΓ
  have hrange : (Pa.comp L).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hmap := hφ.map_nhds_eq_of_surj hrange
  have htr : ∀ q : MvPolynomial κ ℤ, (∀ᶠ w in 𝓝 w₀, aeval (Γ w) (rename a q) = 0) → q = 0 := by
    intro q hq
    refine eq_zero_of_eventually q (fun k => Γ w₀ (a k)) ?_
    rw [← hmap, Filter.eventually_map]
    exact hq.mono fun w hw => by rw [aeval_rename] at hw; exact hw
  let x : κ → MvPolynomial σ ℤ ⧸ P := fun k => Ideal.Quotient.mk P (X (a k))
  have hx : ∀ q : MvPolynomial κ ℤ, aeval x q = Ideal.Quotient.mk P (rename a q) := by
    intro q
    have hh : (aeval x : MvPolynomial κ ℤ →ₐ[ℤ] MvPolynomial σ ℤ ⧸ P) =
        (Ideal.Quotient.mkₐ ℤ P).comp (rename a) := by
      ext k
      simp [x]
    rw [hh]
    rfl
  have hind : AlgebraicIndependent ℤ x := by
    rw [algebraicIndependent_iff_injective_aeval]
    refine (injective_iff_map_eq_zero _).2 fun q hq => htr q ?_
    rw [hx, Ideal.Quotient.eq_zero_iff_mem] at hq
    exact hv _ hq
  have hgbar : Ideal.Quotient.mk P g ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have htrans : Transcendental (Algebra.adjoin ℤ (Set.range x)) (Ideal.Quotient.mk P g) := by
    intro halg
    obtain ⟨r, hr0, t, ht⟩ := halg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hgbar)
    have ht' : (r : MvPolynomial σ ℤ ⧸ P) = Ideal.Quotient.mk P g * t := ht
    have hr : (r : MvPolynomial σ ℤ ⧸ P) ∈ (aeval (R := ℤ) x).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact r.2
    obtain ⟨q, hq⟩ := hr
    have hq' : aeval x q = (r : MvPolynomial σ ℤ ⧸ P) := hq
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective t
    have hmem : rename a q - g * h ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hx, hq', ht', sub_self]
    have hq0 : q = 0 := htr q (((hv _ hmem).and hg0).mono fun w hw => by
      have h1 := hw.1
      rw [map_sub, map_mul, hw.2, zero_mul, sub_zero] at h1
      exact h1)
    apply hr0
    rw [hq0, map_zero] at hq'
    exact Subtype.ext (by simpa using hq'.symm)
  have hc := ((hind.option_iff_transcendental _).2 htrans).cardinalMk_le_trdeg
  rw [Cardinal.mk_option, Cardinal.mk_fintype, hcard] at hc
  have hlt := hc.trans hP
  exact absurd hlt (by norm_cast; omega)

end SheetDecomposition.ChartAlg
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsAlg
section
noncomputable section

namespace SheetDecomposition.CovAlg

open Polynomial

def mon {R : Type} [CommRing R] {d : ℕ} (a : Fin d → R) : R[X] := X ^ d + ∑ j, C (a j) * X ^ (j : ℕ)

def low {R : Type} [CommRing R] {d : ℕ} (a : Fin d → R) : R[X] := ∑ j, C (a j) * X ^ (j : ℕ)

theorem mon_map {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (a : Fin d → R) (f : R →+* S) :
    (mon a).map f = mon fun j => f (a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mon, Polynomial.map_sum]

theorem eval₂_low {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (a : Fin d → R) (f : R →+* S) (x : S) :
    eval₂ f x (low a) = ∑ j, f (a j) * x ^ (j : ℕ) := by
  simp [low, eval₂_finsetSum]

theorem mon_monic {R : Type} [CommRing R] {d : ℕ} (a : Fin d → R) : (mon a).Monic :=
  monic_X_pow_add (degree_sum_fin_lt a)

theorem exists_prim (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] [Algebra Ω₀ Ω] (d : ℕ) (hd : 0 < d)
    (hfin : Module.finrank Ω₀ Ω = d) {σ : Type} [Fintype σ] (t : σ → Ω)
    (ht : Algebra.adjoin Ω₀ (Set.range t) = ⊤) (γ : Ω) :
    ∃ (θ : Ω) (T : Set Ω₀), T.Finite ∧ ∀ (R : Type) [CommRing R] (i : R →+* Ω₀), Function.Injective i →
      T ⊆ Set.range i → ∃ (a : Fin d → R) (cf : σ → Fin d → R) (G : R[X]) (Q : MvPolynomial σ R),
        (mon a).Separable ∧ (∀ F : R[X], eval₂ ((algebraMap Ω₀ Ω).comp i) θ F = 0 ↔ mon a ∣ F) ∧
        (∀ s, eval₂ ((algebraMap Ω₀ Ω).comp i) θ (low (cf s)) = t s) ∧
        eval₂ ((algebraMap Ω₀ Ω).comp i) θ G = γ ∧ MvPolynomial.eval₂ ((algebraMap Ω₀ Ω).comp i) t Q = θ := by
  classical
  haveI : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  haveI : CharZero Ω₀ := (algebraMap Ω₀ Ω).charZero
  let pb := Field.powerBasisOfFiniteOfSeparable Ω₀ Ω
  obtain rfl : pb.dim = d := pb.finrank.symm.trans hfin
  have hint : IsIntegral Ω₀ pb.gen := pb.isIntegral_gen
  let a₀ : Fin pb.dim → Ω₀ := fun j => (minpoly Ω₀ pb.gen).coeff j
  have hP : mon a₀ = minpoly Ω₀ pb.gen := by
    conv_rhs => rw [(minpoly.monic hint).as_sum, pb.natDegree_minpoly, Finset.sum_range]
    rfl
  let cf₀ : σ → Fin pb.dim → Ω₀ := fun s j => pb.basis.repr (t s) j
  have hcf : ∀ s, ∑ j, algebraMap Ω₀ Ω (cf₀ s j) * pb.gen ^ (j : ℕ) = t s := fun s => by
    conv_rhs => rw [← pb.basis.sum_repr (t s)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pb.basis_eq_pow, Algebra.smul_def]
  obtain ⟨G₀, hG₀⟩ := pb.exists_eq_aeval' γ
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : MvPolynomial σ Ω₀, MvPolynomial.aeval t Q₀ = pb.gen := by
    have : pb.gen ∈ Algebra.adjoin Ω₀ (Set.range t) := ht ▸ Algebra.mem_top
    rw [Algebra.adjoin_range_eq_range_aeval] at this
    exact this
  obtain ⟨u₀, v₀, huv⟩ : (minpoly Ω₀ pb.gen).Separable := Algebra.IsSeparable.isSeparable Ω₀ pb.gen
  refine ⟨pb.gen, Set.range a₀ ∪ Set.range (fun q : σ × Fin pb.dim => cf₀ q.1 q.2) ∪ G₀.coeffs ∪ Q₀.coeffs ∪
    u₀.coeffs ∪ v₀.coeffs, by
      simp only [Set.finite_union, Set.finite_range, Finset.finite_toSet, and_self], ?_⟩
  intro R _ i hi hT
  simp only [Set.union_subset_iff] at hT
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hT
  choose a ha using fun j => h1 ⟨j, rfl⟩
  choose cf hcf' using fun s j => h2 ⟨(s, j), rfl⟩
  obtain ⟨G, hG⟩ := (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 h3)
  obtain ⟨u, hu⟩ := (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 h5)
  obtain ⟨v, hv⟩ := (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 h6)
  obtain ⟨Q, hQ⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.2 h4
  have hm : (mon a).map i = minpoly Ω₀ pb.gen := by
    rw [mon_map, ← hP]
    exact congrArg mon (funext ha)
  have hev : ∀ F : R[X], eval₂ ((algebraMap Ω₀ Ω).comp i) pb.gen F = aeval pb.gen (F.map i) := fun F => by
    rw [aeval_def, eval₂_map]
  refine ⟨a, cf, G, Q, ⟨u, v, ?_⟩, fun F => ?_, fun s => ?_, ?_, ?_⟩
  · apply map_injective i hi
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, hm, hu, hv, huv,
      Polynomial.map_one]
  · rw [hev, ← map_dvd_map i hi (mon_monic a), hm, minpoly.dvd_iff]
  · rw [eval₂_low, ← hcf s]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RingHom.comp_apply, hcf']
  · rw [hev, hG, hG₀]
  · rw [← MvPolynomial.eval₂_map, hQ, ← hQ₀, MvPolynomial.aeval_def]

end SheetDecomposition.CovAlg
end
end

