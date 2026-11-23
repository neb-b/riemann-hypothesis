module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraMapBasicOpen
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

theorem exists_linear_mod_sq {A : Type} [CommRing A] [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι → A) (hr : Algebra.adjoin ℂ (Set.range r) = ⊤) (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (a : A) (ha : e a = 0) :
    ∃ c : ι → ℂ, a - ∑ l, c l • (r l - algebraMap ℂ A (e (r l))) ∈ RingHom.ker e ^ 2 := by
  have hK : ∀ x : A, x - algebraMap ℂ A (e x) ∈ RingHom.ker e := fun x => by
    rw [RingHom.mem_ker, map_sub, he, sub_self]
  have hP : ∀ x, ∃ c : ι → ℂ,
      x - algebraMap ℂ A (e x) - ∑ l, c l • (r l - algebraMap ℂ A (e (r l))) ∈ RingHom.ker e ^ 2 := by
    intro x
    have hx : x ∈ Algebra.adjoin ℂ (Set.range r) := hr ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      refine ⟨Pi.single l 1, ?_⟩
      have hs : ∑ l', (Pi.single l 1 : ι → ℂ) l' • (r l' - algebraMap ℂ A (e (r l'))) =
          r l - algebraMap ℂ A (e (r l)) := by
        rw [Finset.sum_eq_single l]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · simp
      rw [hs, sub_self]
      exact zero_mem _
    | algebraMap c =>
      refine ⟨0, ?_⟩
      simp [he]
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨c + d, ?_⟩
      have h : x + y - algebraMap ℂ A (e (x + y)) - ∑ l, (c + d) l • (r l - algebraMap ℂ A (e (r l))) =
          (x - algebraMap ℂ A (e x) - ∑ l, c l • (r l - algebraMap ℂ A (e (r l)))) +
          (y - algebraMap ℂ A (e y) - ∑ l, d l • (r l - algebraMap ℂ A (e (r l)))) := by
        simp only [map_add (f := _), Pi.add_apply, add_smul, Finset.sum_add_distrib]
        ring
      rw [h]
      exact add_mem hc hd
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨e x • d + e y • c, ?_⟩
      have h : x * y - algebraMap ℂ A (e (x * y)) -
            ∑ l, (e x • d + e y • c) l • (r l - algebraMap ℂ A (e (r l))) =
          algebraMap ℂ A (e x) * (y - algebraMap ℂ A (e y) - ∑ l, d l • (r l - algebraMap ℂ A (e (r l)))) +
          algebraMap ℂ A (e y) * (x - algebraMap ℂ A (e x) - ∑ l, c l • (r l - algebraMap ℂ A (e (r l)))) +
          (x - algebraMap ℂ A (e x)) * (y - algebraMap ℂ A (e y)) := by
        have hsum : ∑ l, (e x • d + e y • c) l • (r l - algebraMap ℂ A (e (r l))) =
            e x • ∑ l, d l • (r l - algebraMap ℂ A (e (r l))) +
              e y • ∑ l, c l • (r l - algebraMap ℂ A (e (r l))) := by
          rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, add_smul, smul_eq_mul, smul_eq_mul, mul_smul,
            mul_smul]
        rw [hsum, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
        ring
      have hxy : (x - algebraMap ℂ A (e x)) * (y - algebraMap ℂ A (e y)) ∈ RingHom.ker e ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul (hK x) (hK y)
      rw [h]
      exact add_mem (add_mem (Ideal.mul_mem_left _ _ hd) (Ideal.mul_mem_left _ _ hc)) hxy
  obtain ⟨c, hc⟩ := hP a
  rw [ha, map_zero, sub_zero] at hc
  exact ⟨c, hc⟩

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {N : ℕ}

theorem algebraMap_basicOpen {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1) (c : ℂ) :
    algebraMap ℂ Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g) c =
      (Proj.awayToSection (grading ℂ N) g).hom
        (HomogeneousLocalization.fromZeroRingHom (grading ℂ N) _ (algebraMap ℂ (grading ℂ N 0) c)) := by
  have h := GlobalTheory.QCoh.Qcqs.baseRingHom_comp_SpecMap (Proj.toSpecZero (grading ℂ N))
    (CommRingCat.ofHom (algebraMap ℂ (grading ℂ N 0))) (Proj.basicOpen (grading ℂ N) g)
  have h' := ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen (grading ℂ N) hg one_pos
  rw [GlobalTheory.QCoh.Qcqs.baseRingHom.eq_1 (Proj.toSpecZero _), h'] at h
  exact congrArg (fun φ => φ.hom c) h

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {N : ℕ}

theorem frac_eq_aeval {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1) (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) ℂ) (hf : f ∈ grading ℂ N (n • 1)) :
    frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g) f (g ^ n) hf (SetLike.pow_mem_graded n hg)
        (fun x hx h => hx (x.isPrime.mem_of_pow_mem n h)) =
      MvPolynomial.aeval (fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g) (MvPolynomial.X l) g
        (X_mem ℂ N l) hg le_rfl) f := by
  refine ext fun x hx => ?_
  let t : Localization.AtPrime x.asHomogeneousIdeal.toIdeal := Localization.mk 1 ⟨g, hx⟩
  have hC : (ev (grading ℂ N) _ x hx).comp (algebraMap ℂ Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g)) =
      (algebraMap (MvPolynomial (Fin (N + 1)) ℂ) _).comp MvPolynomial.C := by
    ext c
    simp only [RingHom.comp_apply]
    rw [algebraMap_basicOpen hg, awayToSection_fromZero, ev_frac, ← Localization.mk_one_eq_algebraMap]
    rfl
  have hX : ∀ l, ev (grading ℂ N) _ x hx (frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g) (MvPolynomial.X l) g
        (X_mem ℂ N l) hg le_rfl) = algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (MvPolynomial.X l) * t := by
    intro l
    rw [ev_frac, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    congr 1
    · simp
    · ext1; simp
  have hf' : f.IsHomogeneous n := by simpa using hf
  erw [ev_frac]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hC]
  have hfun : (ev (grading ℂ N) _ x hx ∘ fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g)
      (MvPolynomial.X l) g (X_mem ℂ N l) hg le_rfl) =
      fun l => algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (MvPolynomial.X l) * t := funext hX
  rw [hfun, ReciprocityTheory.AnForm.R.eval₂_mul_const_of_isHomogeneous _ _ _ hf']
  have h3 : MvPolynomial.eval₂ ((algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal)).comp MvPolynomial.C)
      (fun l => algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (MvPolynomial.X l)) f = algebraMap _ _ f := by
    have := MvPolynomial.eval₂_comp_left (algebraMap (MvPolynomial (Fin (N + 1)) ℂ)
      (Localization.AtPrime x.asHomogeneousIdeal.toIdeal)) MvPolynomial.C MvPolynomial.X f
    rw [MvPolynomial.eval₂_eta] at this
    exact this.symm
  rw [h3, Localization.mk_pow, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  congr 1
  · simp
  · ext1; simp

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {N : ℕ}

theorem mem_adjoin_frac {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1)
    (s : Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g)) :
    s ∈ Algebra.adjoin ℂ (Set.range fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g)
      (MvPolynomial.X l) g (X_mem ℂ N l) hg le_rfl) := by
  obtain ⟨y, rfl⟩ := (Proj.basicOpenIsoAway (grading ℂ N) g hg one_pos).commRingCatIsoToRingEquiv.surjective s
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hg y
  change (Proj.awayToSection (grading ℂ N) g).hom _ ∈ _
  rw [awayToSection_mk, frac_eq_aeval hg n f hf, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨f, rfl⟩

theorem adjoin_fRatio_eq_top {S : Scheme.{0}} (p : S ⟶ Sp ℂ) (ι : S ⟶ PSpace ℂ N) [IsClosedImmersion ι]
    (hp : ι ≫ PSpace.str ℂ N = p) {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1) :
    Algebra.adjoin (A := Sec p (fOpen ι g)) ℂ
      (Set.range fun l => fRatio ι (MvPolynomial.X l) g (X_mem ℂ N l) hg) = ⊤ := by
  subst hp
  let ψ : Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g) →ₐ[ℂ] Sec (ι ≫ PSpace.str ℂ N) (fOpen ι g) :=
    { (ι.app (Proj.basicOpen (grading ℂ N) g)).hom with
      commutes' := fun c => GlobalTheory.QCoh.Qcqs.app_baseRingHom ι (PSpace.str ℂ N) _ c }
  have hsurj : Function.Surjective ψ :=
    ι.app_surjective _ (Proj.isAffineOpen_basicOpen (grading ℂ N) g hg one_pos)
  rw [eq_top_iff]
  intro a _
  obtain ⟨s, rfl⟩ := hsurj a
  have h1 : ψ s ∈ (Algebra.adjoin ℂ (Set.range fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g)
      (MvPolynomial.X l) g (X_mem ℂ N l) hg le_rfl)).map ψ := Subalgebra.mem_map.2 ⟨s, mem_adjoin_frac hg s, rfl⟩
  rw [AlgHom.map_adjoin, ← Set.range_comp] at h1
  exact h1

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

theorem ratio_span_cotangent : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ (g : MvPolynomial (Fin (N + 1)) ℂ) (hg : g ∈ GlobalTheory.ProjSpace.grading ℂ N 1) (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι g)), let U := GlobalTheory.EtProj.fOpen ι g; let r : Fin (N + 1) → Sec p U := fun l => GlobalTheory.EtProj.fRatio ι (MvPolynomial.X l) g (GlobalTheory.ProjSpace.X_mem ℂ N l) hg; let e : Sec p U →+* ℂ := CxPts.evHom hy; ∀ a : Sec p U, e a = 0 → ∃ c : Fin (N + 1) → ℂ, a - ∑ l, c l • (r l - algebraMap ℂ (Sec p U) (e (r l))) ∈ RingHom.ker e ^ 2 := by
  intro X p N ι hι hp g hg y hy U r e a ha
  have hr : Algebra.adjoin ℂ (Set.range r) = ⊤ := adjoin_fRatio_eq_top p ι hp hg
  have he : ∀ c : ℂ, e (algebraMap ℂ (Sec p U) c) = c := fun c =>
    (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)
  exact exists_linear_mod_sq r hr e he a ha

end GlobalTheory.EtProj.RatSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmHostRankBounds
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.W1

theorem dv_mem_span_of_formallyUnramified : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.FormallyUnramified → ∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → L) (w : Fin m → K), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D k L v) = ∑ j, b j • mapDR k K L (ι1 (D k K (w j))) := by
  intro k K L _ _ _ _ _ _ _ B B' φ hφ hU v hv
  letI := φ.toAlgebra
  haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    change algebraMap k L c = ((φ (algebraMap k B c) : B') : L)
    rw [hφ, IsScalarTower.algebraMap_apply k K L]
    rfl
  haveI : Algebra.FormallyUnramified B B' := hU
  have hspan : Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map k B B' x).mp (Subsingleton.elim _ _)
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hm : m ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨a, rfl⟩
      | zero => simp
      | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul B' a]
        exact Submodule.smul_mem _ _ hx
  have hmem : KaehlerDifferential.D k B' ⟨v, hv⟩ ∈
      Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) := hspan ▸ Submodule.mem_top
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.mp hmem
  choose w hw using fun j => (g j).2
  refine ⟨n, fun j => (f j : L), fun j => (w j : K), fun j => ⟨(f j).2, (w j).2⟩, ?_⟩
  have key : KaehlerDifferential.D k L v = ∑ j, (f j : L) • KaehlerDifferential.D k L (algebraMap K L (w j)) := by
    have h := congrArg (KaehlerDifferential.map k k B' L) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, KaehlerDifferential.map_D] at h
    refine h.symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← hw j, KaehlerDifferential.map_D, ← hφ]
    first | rfl | simp [Subalgebra.smul_def]
  have hpull : ∀ a : K, mapDR k K L (ι1 (D k K a)) = ι1 (D k L (algebraMap K L a)) := by
    intro a
    rw [mapDR, ExteriorAlgebra.lift_ι_apply]
    simp [map1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [hpull, key, map_sum, map_smul]

end GlobalTheory.W1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqTopOfForallComplexPointsMemOpens
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MaxPt

theorem eq_top_of_forall_cxPts_mem : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens),
    (∀ z : CxPts p (RingHom.id ℂ), z ∈ CxPts.ptsIn p (RingHom.id ℂ) U) → U = ⊤ := by
  intro X p _ U hall
  by_contra hU
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ U := by
    by_contra h
    push_neg at h
    exact hU (eq_top_iff.2 fun y _ => h y)
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hV : IsAffineOpen V := hV
  let S : Set (PrimeSpectrum Γ(X, V)) := {η | hV.fromSpec η ∉ U}
  have hS : IsClosed S := by
    have : IsOpen {η : PrimeSpectrum Γ(X, V) | hV.fromSpec η ∈ U} :=
      U.isOpen.preimage hV.fromSpec.continuous
    exact this.isClosed_compl
  have hSne : S.Nonempty := by
    have : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hxV
    obtain ⟨ξ, hξ⟩ := this
    exact ⟨ξ, by show hV.fromSpec ξ ∉ U; rw [hξ]; exact hx⟩
  obtain ⟨η, hηS, hηc⟩ := hS.exists_closed_singleton hSne
  have hm : η.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal η).1 hηc
  set m := η.asIdeal
  have h1 := LocallyOfFiniteType.finiteType_appLE p (isAffineOpen_top (Sp ℂ)) hV (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p V).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, V) := (algX p V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, V) := hft
  letI : Field (Γ(X, V) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(X, V) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(X, V) ⧸ m)
  have hbij : Function.Bijective (algebraMap ℂ (Γ(X, V) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃+* (Γ(X, V) ⧸ m) := RingEquiv.ofBijective _ hbij
  let φ : Γ(X, V) →+* ℂ := (e.symm : (Γ(X, V) ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m)
  have hφ : ∀ a, φ (algX p V a) = (RingHom.id ℂ) a := by
    intro a
    show e.symm (Ideal.Quotient.mk m (algebraMap ℂ Γ(X, V) a)) = a
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.symm_apply_apply a
  have hker : RingHom.ker φ = m := by
    ext f
    rw [RingHom.mem_ker]
    show e.symm (Ideal.Quotient.mk m f) = 0 ↔ f ∈ m
    rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  have hz := CxPts.mem_ptsIn.1 (hall (CxPts.ofHom hV φ hφ))
  have hpt : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ) = η := by
    apply PrimeSpectrum.ext
    show Ideal.comap φ (IsLocalRing.maximalIdeal ℂ) = m
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]
  have : (CxPts.ofHom hV φ hφ).1 (IsLocalRing.closedPoint ℂ) = hV.fromSpec η := by
    show (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) (IsLocalRing.closedPoint ℂ) = _
    show hV.fromSpec (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint ℂ)) = _
    rw [hpt]
  exact hηS (this ▸ hz)

end GlobalTheory.MaxPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexPointKerEvalEqMaximal
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MaxPt

theorem exists_cxPts_ker_eq : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ m : Ideal Γ(X, U), m.IsMaximal → ∃ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
      m = RingHom.ker (CxPts.evHom hy) := by
  intro X p _ U hU m hm
  have h1 := p.finiteType_appLE (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, U) := hft
  haveI : m.IsMaximal := hm
  letI : Field (Γ(X, U) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(X, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(X, U) ⧸ m)
  have hbij : Function.Bijective (algebraMap ℂ (Γ(X, U) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃+* (Γ(X, U) ⧸ m) := RingEquiv.ofBijective _ hbij
  let φ : Γ(X, U) →+* ℂ := (e.symm : (Γ(X, U) ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m)
  have hφ : ∀ a, φ (algX p U a) = (RingHom.id ℂ) a := by
    intro a
    show e.symm (Ideal.Quotient.mk m (algebraMap ℂ Γ(X, U) a)) = a
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.symm_apply_apply a
  refine ⟨CxPts.ofHom hU φ hφ, CxPts.ofHom_mem hU φ hφ, ?_⟩
  have hev : CxPts.evHom (CxPts.ofHom_mem hU φ hφ) = φ := by
    ext f
    rw [← CxPts.ev_eq, CxPts.ev_ofHom]
  rw [hev]
  ext f
  rw [RingHom.mem_ker]
  show f ∈ m ↔ e.symm (Ideal.Quotient.mk m f) = 0
  rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.MaxPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsProjFormNonvanishingGenericPointComplexPoi
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

theorem exists_form_forall_notMem (N n : ℕ) (T : Finset (PSpace ℂ N)) :
    ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n, ∀ x ∈ T, f ∉ x.asHomogeneousIdeal := by
  classical
  let V : T → Submodule ℂ (GlobalTheory.ProjSpace.grading ℂ N 1) := fun x =>
    ((x.1.asHomogeneousIdeal.toIdeal).restrictScalars ℂ).comap (GlobalTheory.ProjSpace.grading ℂ N 1).subtype
  have hV : ∀ x, V x ≠ ⊤ := by
    intro x h
    obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart ℂ N x.1
    have hX : (⟨MvPolynomial.X i, GlobalTheory.ProjSpace.X_mem ℂ N i⟩ : GlobalTheory.ProjSpace.grading ℂ N 1) ∈ V x :=
      h ▸ Submodule.mem_top
    exact (Proj.mem_basicOpen _ _ _).1 hi hX
  obtain ⟨ℓ, hℓ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top V hV
  have hpow : ℓ.1 ^ n ∈ GlobalTheory.ProjSpace.grading ℂ N n := by
    simpa using SetLike.pow_mem_graded n ℓ.2
  refine ⟨ℓ.1 ^ n, hpow, fun x hx hmem => hℓ ⟨x, hx⟩ ?_⟩
  exact x.isPrime.mem_of_pow_mem n hmem

theorem exists_form_genericPoint_cxPts : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (N : ℕ)
    (ι : X ⟶ PSpace ℂ N) (n : ℕ) (F : Finset (CxPts p (RingHom.id ℂ))), ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n,
      genericPoint X ∈ GlobalTheory.EtProj.fOpen ι f ∧ ∀ z ∈ F, z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f) := by
  intro X _ p N ι n F
  classical
  obtain ⟨f, hf, hT⟩ := exists_form_forall_notMem N n
    (insert (ι.base (genericPoint X)) (F.image fun z => ι.base (z.1 (IsLocalRing.closedPoint ℂ))))
  refine ⟨f, hf, hT _ (Finset.mem_insert_self _ _), fun z hz => ?_⟩
  exact CxPts.mem_ptsIn.2 (hT _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz)))

end GlobalTheory.EtProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureOfFiniteMapIntegrallyClosedSubrin
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem integralClosure_of_finite_map : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → IsIntegrallyClosed B → IsIntegrallyClosed B' → (∀ x : K, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → (∀ y ∈ B', IsIntegral B (y : L)) ∧ (∀ x : K, IsIntegral B x → x ∈ B) ∧ (∀ y : L, IsIntegral B y → y ∈ B') := by
  intro k K L _ _ _ _ _ _ _ B B' φ hφ hfin hB hB' hK hL
  letI : Algebra B B' := φ.toAlgebra
  haveI : IsScalarTower B B' L := IsScalarTower.of_algebraMap_eq fun x => (hφ x).symm
  have fracK : IsFractionRing B K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hK z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [eq_div_iff hb0, h]
  have fracL : IsFractionRing B' L := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hL z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [eq_div_iff hb0, h]
  have hint : (algebraMap B B').IsIntegral := RingHom.Finite.to_isIntegral hfin
  refine ⟨fun y hy => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : IsIntegral B (⟨y, hy⟩ : B') := hint _
    have := h1.algebraMap (B := L)
    simpa using this
  · obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff K).mp hB hx
    rw [← hc]; exact c.2
  · have h2 : IsIntegral B' y := hy.tower_top
    obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff L).mp hB' h2
    rw [← hc]; exact c.2

end GlobalTheory.W1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFramePolynomialComplexValuesAtPointStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedFramePolynomial_complex_values_at_point : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La' : (sysS H X std).Lt (j + 1)) (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ), P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) → (∀ y, φ (clsAt X H (j + 1) La'.1 La'.2) y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y) → ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj h La' φ V ∧ MvPolynomial.map ι V = scT d S ι j La'.1 La'.2 • GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La' (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j P)) := by
  first | exact @GlobalTheory.TwV.DelA.transported_frame_realAt | exact GlobalTheory.TwV.DelA.transported_frame_realAt | (intros; apply GlobalTheory.TwV.DelA.transported_frame_realAt <;> assumption)
end

