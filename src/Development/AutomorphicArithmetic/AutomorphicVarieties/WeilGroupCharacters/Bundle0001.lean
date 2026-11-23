module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsAlgebraicPointOfGroupDeterminant
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

section SlopeTestRemainingChoices

open Polynomial

private theorem algpt_int {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {R : Type} [CommRing R] [Algebra O R] [IsLocalRing R]
    {K : Type} [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K)
    (a : R) (ha : a ∈ maximalIdeal R) : IsIntegral O (f a) :=
  _root_.UpperTheory.Reformulated.B.AlgebraicPointIntegral.algpt_int f a ha

private theorem algpt_pow {O S : Type} [CommRing O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (m : Ideal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ m) (n : ℕ) :
    ∃ N : Submodule O S, N.FG ∧ ∀ x : S, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow m hres n

private theorem algpt_finite {O S : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing S] [Algebra O S] [IsLocalRing S] [IsNoetherianRing S] [Algebra.IsIntegral O S]
    (hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ maximalIdeal S) : Module.Finite O S := by
  set J : Ideal S := (maximalIdeal O).map (algebraMap O S) with hJ
  have hJle : J ≤ maximalIdeal S := Ideal.map_le_iff_le_comap.2 hloc
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hJle))
  haveI : IsHausdorff (maximalIdeal O) S :=
    IsHausdorff.map_algebraMap_iff.1 (IsHausdorff.of_isLocalRing J S hJne)
  have hrad : maximalIdeal S ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    have h1 : maximalIdeal O ≤ P.comap (algebraMap O S) := Ideal.map_le_iff_le_comap.1 hJP
    have h2 : P.comap (algebraMap O S) = maximalIdeal O :=
      ((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) h1).symm
    have h3 : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (algebraMap O S) (algebraMap_isIntegral_iff.mpr ‹Algebra.IsIntegral O S›) P
      (h2 ▸ maximalIdeal.isMaximal O)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨N, hN, h⟩ := algpt_pow (maximalIdeal S) hres n
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) S).2 ⟨?_⟩
  have : (⊤ : Submodule O (S ⧸ (maximalIdeal O) • (⊤ : Submodule O S))) = N.map (Submodule.mkQ _) := by
    symm
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := h x
    have h2 : x - y ∈ (maximalIdeal O) • (⊤ : Submodule O S) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    simpa using Submodule.add_mem_sup h2 hy
  rw [this]
  exact hN.map _

end SlopeTestRemainingChoices

theorem UpperTheory.V.W.exists_algebraicPoint_of_groupDeterminant :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (K : Type) [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K), Module.Finite O f.range := by
  intro O _ _ _ _ R _ _ _ K _ _ _ _ f
  have hint : ∀ a : R, IsIntegral O (f a) := by
    intro a
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have h1 : IsIntegral O (f (a - algebraMap O R c)) := algpt_int f _ hc
    have h2 : f a = f (a - algebraMap O R c) + algebraMap O _ c := by simp
    rw [h2]
    exact h1.add isIntegral_algebraMap
  let g : R →ₐ[O] f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (g : R →+* f.range) hg
  haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (g : R →+* f.range) hg
  haveI : IsLocalHom (g : R →+* f.range) := IsLocalHom.of_surjective _ hg
  have hm : ∀ a ∈ maximalIdeal R, g a ∈ maximalIdeal f.range := fun a ha =>
    map_nonunit (g : R →+* f.range) a ha
  haveI : Algebra.IsIntegral O f.range := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hg x
    exact (isIntegral_algHom_iff f.range.val Subtype.val_injective).1 (hint a)⟩
  exact algpt_finite
    (fun a ha => by
      rw [← g.commutes]
      exact hm _ (map_nonunit (algebraMap O R) a ha))
    (fun x => by
      obtain ⟨a, rfl⟩ := hg x
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
      exact ⟨c, by simpa using hm _ hc⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

section SlopeTestRemainingChoices

open Polynomial

variable {n : ℕ} {A A' A'' G : Type} [CommRing A] [CommRing A'] [CommRing A''] [Group G]

private theorem pm_map_map (D : GDet n A G) (f : A →+* A') (g : A' →+* A'') :
    (D.map f).map g = D.map (g.comp f) := rfl

private theorem pm_chi_map (D : GDet n A G) (f : A →+* A') (y : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
  letI : Algebra A A'[X] := ((algebraMap A' A'[X]).comp f).toAlgebra
  have h := D.nat A[X] A'[X]
    { (Polynomial.mapRingHom f : A[X] →+* A'[X]) with
      commutes' := fun a => by
        show Polynomial.map f (C a) = C (f a)
        simp }
    (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
  refine Eq.trans ?_ h
  show D.D A'[X] _ = D.D A'[X] (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · clear h
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp

private theorem pm_lam_map (D : GDet n A G) (f : A →+* A') (i : ℕ) (y : MonoidAlgebra A G) :
    (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y) := by
  simp [GDet.lam, pm_chi_map]

private theorem pm_lam_single (D : GDet n A G) (f : A →+* A') (i : ℕ) (g : G) :
    (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  rw [← pm_lam_map]; simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.W.exists_determinantPair_map_of_algHom :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid F O n) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (p : Pair r R), ∃ p' : Pair r R', p.Maps (f : R →+* R') p'.D p'.ψ := by
  intro l _ F O _ _ _ n r R _ _ _ R' _ _ _ f p
  have hle : ∀ N, maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := fun N => by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  have heps : ∀ g, Units.map ((f : R →+* R') : R →* R') (F.eps O R g) = F.eps O R' g := fun g =>
    Units.ext (f.commutes _)
  refine ⟨
    { D := p.D.map (f : R →+* R')
      ψ := fun v i => pushCh (f : R →+* R') (p.ψ v i)
      cont := fun i N => ?_
      red := ?_
      psi := fun v i =>
        { cont := fun N => ((p.psi v i).cont N).comp (Ideal.quotientMap _ (f : R →+* R') (hle N))
          red := fun g => (res_map f _).trans ((p.psi v i).red g)
          mu := fun g => (congrArg f ((p.psi v i).mu g)).trans (f.commutes _) }
      P := fun i g => ?_
      Ord := fun v g h => ?_
      I := fun u g hg h => ?_ }, rfl, fun _ _ => rfl⟩
  · simp only [pm_lam_single]
    exact (p.cont i N).comp (Ideal.quotientMap _ (f : R →+* R') (hle N))
  · rw [pm_map_map, ← p.red]
    congr 1
    exact RingHom.ext (res_map f)
  · have h1 : F.star O R' n (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (F.star O R n (MonoidAlgebra.single g 1)) := by
      simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk, OneHom.coe_mk,
        MulOpposite.unop_op, MonoidAlgebra.mapRingHom_single]
      rw [← heps, ← map_zpow]
      rfl
    rw [h1, pm_lam_map, p.P, pm_lam_single]
  · have h1 : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh (f : R →+* R') (p.ψ v i)) g =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) g) := by
      simp only [GFrame.oEl, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub,
        MonoidAlgebra.mapRingHom_single, map_one]
      rfl
    rw [h1, GDet.tr, pm_lam_map]
    exact (congrArg (f : R →+* R') (p.Ord v g h)).trans (map_zero _)
  · have h1 : MonoidAlgebra.single h (1 : R') * (MonoidAlgebra.single g 1 - 1) =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) := by
      simp only [map_mul, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
    rw [h1, GDet.tr, pm_lam_map]
    exact (congrArg (f : R →+* R') (p.I u g hg h)).trans (map_zero _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairPullback
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.W.FramePullback

section Det

variable {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]

private theorem chi_comap (D : GDet n A G) (φ : H →* G) (y : MonoidAlgebra A H) :
    (D.comap φ).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A φ y) := by
  change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp

private theorem lam_comap (D : GDet n A G) (φ : H →* G) (i : ℕ) (y : MonoidAlgebra A H) :
    (D.comap φ).lam i y = D.lam i (MonoidAlgebra.mapDomainRingHom A φ y) := by
  unfold GDet.lam
  rw [chi_comap]

private theorem tr_zero (D : GDet n A G) (hn : 1 ≤ n) : D.tr 0 = 0 := by
  have h1 : D.chi 0 = Polynomial.X ^ n := by
    have := D.homog (Polynomial A) Polynomial.X 1
    rw [map_one, mul_one] at this
    rw [← this, GDet.chi, map_zero, sub_zero]
    congr 1
    simp [MonoidAlgebra.one_def]
  unfold GDet.tr GDet.lam
  rw [h1, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

private theorem tr_dim_zero (D : GDet 0 A G) (y : MonoidAlgebra A G) : D.tr y = -1 := by
  have h1 : ∀ x, D.D (Polynomial A) x = D.D (Polynomial A) 0 := fun x => by
    have := D.homog (Polynomial A) 0 x
    rw [zero_smul, pow_zero, one_mul] at this
    exact this.symm
  have h2 : D.chi y = 1 := by rw [GDet.chi, h1, ← h1 1, map_one]
  unfold GDet.tr GDet.lam
  rw [h2]
  simp

private theorem ofRep_comap (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) :
    (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg]

end Det

private theorem adic_comp {Γ Γ' R : Type} [TopologicalSpace Γ] [TopologicalSpace Γ'] [CommRing R] {I : Ideal R}
    {f : Γ → R} (hf : AdicCont I f) {φ : Γ' → Γ} (hφ : Continuous φ) : AdicCont I fun x => f (φ x) :=
  fun m => (hf m).comp_continuous hφ

private theorem mu_map {l : ℕ} [Fact l.Prime] {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : G →* H) (hφ : Continuous φ) {g : G}
    (hg : g ∈ muG l G) : φ g ∈ muG l H := by
  obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.1 hg
  refine CommGroup.mem_primaryComponent.2 ⟨k, ?_⟩
  have h1 : g ^ l ^ k ∈ (commutator G).topologicalClosure := (QuotientGroup.eq_one_iff _).1 hk
  have h2 : (commutator G).topologicalClosure ≤ (commutator H).topologicalClosure.comap φ := by
    refine Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_topologicalClosure _).preimage hφ)
    refine le_trans ?_ (Subgroup.comap_mono (Subgroup.le_topologicalClosure _))
    rw [← Subgroup.map_le_iff_le_comap, commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have h3 : φ g ^ l ^ k ∈ (commutator H).topologicalClosure := by
    rw [← map_pow]; exact h2 h1
  exact (QuotientGroup.eq_one_iff _).2 h3

variable {l : ℕ} [Fact l.Prime] {F' F : GFrame l} (h : FHom F' F)

private theorem continuous_pullback_projection : Continuous h.π₀ := (h.π_cont.comp (continuous_subtype_val : Continuous (fun x : F'.G₀ => (x : F'.Γ)))).subtype_mk _

private theorem pullback_projection_frobenius (v) (g) : h.π₀ (F'.φ v g) = F.φ (h.vl v) (h.gv v g) := Subtype.ext (h.hφ v g).symm

private theorem pullback_projection_conj (g) : h.π₀ (F'.conj g) = F.conj (h.π₀ g) := by
  apply Subtype.ext
  change h.π (F'.c * g * F'.c⁻¹) = F.c * h.π g * F.c⁻¹
  rw [map_mul, map_mul, map_inv, h.hc]

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R]

private theorem pullback_projection_sign_eq (g) : F.eps O R (h.π₀ g) = F'.eps O R g := by
  change Units.map _ (F.ε (h.π g)) = Units.map _ (F'.ε g)
  rw [h.hε]

private theorem star_single (F : GFrame l) (n : ℕ) (g : F.G₀) :
    F.star O R n (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) := by
  simp [GFrame.star, GFrame.starOp]

private theorem map_star0 (n : ℕ) (g : F'.G₀) :
    MonoidAlgebra.mapDomainRingHom R h.π₀ (F'.star O R n (MonoidAlgebra.single g 1)) =
      F.star O R n (MonoidAlgebra.single (h.π₀ g) 1) := by
  rw [star_single, star_single, pullback_projection_sign_eq, ← pullback_projection_conj, ← map_inv]
  simp

private theorem map_oEl {n : ℕ} (v : F'.Vl) (ψ : Fin n → F.Gv (h.vl v) →* Rˣ) (g : Fin n → F'.Gv v) :
    MonoidAlgebra.mapDomainRingHom R h.π₀ (F'.oEl v (fun i => (ψ i).comp (h.gv v)) g) =
      F.oEl (h.vl v) ψ fun i => h.gv v (g i) := by
  unfold GFrame.oEl
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  rw [Function.comp_apply, map_sub]
  simp [pullback_projection_frobenius]

end UpperTheory.V.W.FramePullback


open UpperTheory.V.W.FramePullback in
theorem UpperTheory.V.W.Pair.isEmpty_of_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R)
    (hn : n = 0) : IsEmpty F.St ∧ IsEmpty F.Vl := by
  subst hn
  refine ⟨⟨fun u => ?_⟩, ⟨fun v => ?_⟩⟩
  · have := p.I u 1 (one_mem _) 1
    rw [tr_dim_zero] at this
    exact one_ne_zero (neg_eq_zero.1 this)
  · have := p.Ord v (fun _ => 1) 1
    rw [tr_dim_zero] at this
    exact one_ne_zero (neg_eq_zero.1 this)

open UpperTheory.V.W.FramePullback in
theorem UpperTheory.V.W.exists_determinantPair_pullback :
    ∀ (l : ℕ) [Fact l.Prime] (F' F : GFrame l) (h : FHom F' F) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r' : Resid F' O n) (r : Resid F O n), h.Compat r' r → (n = 0 → IsEmpty F'.St) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R),
      ∃ p' : Pair r' R, p'.D = p.D.comap h.π₀ ∧ ∀ v i, p'.ψ v i = (p.ψ (h.vl v) i).comp (h.gv v) := by
  intro l _ F' F h O _ _ _ n r' r hc hn R _ _ _ p
  have hs : ∀ g : F'.G₀, MonoidAlgebra.mapDomainRingHom R h.π₀ (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (h.π₀ g) 1 := fun g => by simp
  refine ⟨⟨p.D.comap h.π₀, fun v i => (p.ψ (h.vl v) i).comp (h.gv v), fun i => ?_, ?_, fun v i => ⟨?_, fun g => ?_, fun g => ?_⟩,
    fun i g => ?_, fun v g k => ?_, fun u g hg k => ?_⟩, rfl, fun _ _ => rfl⟩
  · simp only [lam_comap, hs]
    exact adic_comp (p.cont i) (continuous_pullback_projection h)
  · have : (p.D.comap h.π₀).map (res O R : R →+* ResidueField O) =
        (p.D.map (res O R : R →+* ResidueField O)).comap h.π₀ := rfl
    rw [this, p.red, Resid.Dbar, ofRep_comap, Resid.Dbar]
    congr 1
    ext g : 1
    have e : r'.chib = fun i => (r.chib i).comp h.π₀ := funext hc.chib
    rw [e]; rfl
  · exact adic_comp (p.psi (h.vl v) i).cont (h.gv_cont v)
  · rw [hc.psib]
    exact (p.psi (h.vl v) i).red _
  · have hg : h.gv v g ∈ F.mu (h.vl v) := mu_map (h.gv v) (h.gv_cont v) g.2
    rw [hc.th v i g hg]
    exact (p.psi (h.vl v) i).mu ⟨_, hg⟩
  · rw [lam_comap, lam_comap, map_star0, hs, p.P]
  · rw [GDet.tr, lam_comap, map_mul, hs, map_oEl]
    exact p.Ord _ _ _
  · rw [GDet.tr, lam_comap, map_mul, map_sub, hs, hs, map_one]
    rcases hc.ip u g hg with h1 | ⟨u', hu'⟩
    · rw [h1, ← MonoidAlgebra.one_def, sub_self, mul_zero]
      exact tr_zero p.D (Nat.pos_of_ne_zero fun h0 => (hn h0).elim u)
    · exact p.I u' _ hu' _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamZl
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

private theorem zl_pow {R : Type} [CommRing R] (I : Ideal R) (l : ℕ) (hl : (l : R) ∈ I) (u : R) (hu : u - 1 ∈ I)
    (N : ℕ) : u ^ l ^ N - 1 ∈ I ^ (N + 1) := by
  induction N with
  | zero => simpa using hu
  | succ N ih =>
    have h1 : u ^ l ^ N - 1 ∈ I := Ideal.pow_le_self (Nat.succ_ne_zero N) ih
    rw [pow_succ l, pow_mul, ← mul_geom_sum, pow_succ I]
    refine Ideal.mul_mem_mul ih ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hl h1 ⊢
    rw [map_sub, map_one, sub_eq_zero] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_pow _ (u ^ l ^ N), h1, one_pow]
    simpa using hl

private theorem zl_eq {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R] {a b : R}
    (h : ∀ n, Ideal.Quotient.mk (I ^ n) a = Ideal.Quotient.mk (I ^ n) b) : a = b :=
  sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact Ideal.Quotient.eq.1 (h n))

private theorem zl_lc (l : ℕ) [Fact l.Prime] (N : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow N : ℤ_[l] → ZMod (l ^ N)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hp : (0 : ℝ) < (l : ℝ) ^ (-N : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hp] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, sub_eq_zero] at hy
  exact hy

private theorem zl_one (l : ℕ) [Fact l.Prime] {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (hl : (l : R) ∈ I) (u : Rˣ) (hu : (u : R) - 1 ∈ I) :
    ∃ χ : Multiplicative ℤ_[l] →* Rˣ, AdicCont I (fun x => ((χ x : Rˣ) : R)) ∧ χ (Multiplicative.ofAdd 1) = u := by
  have hl0 : ∀ N, NeZero (l ^ N) := fun N => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hB : ∀ N (a b : ℕ), (a : ZMod (l ^ N)) = b →
      Ideal.Quotient.mk (I ^ N) (u ^ a) = Ideal.Quotient.mk (I ^ N) (u ^ b) := fun N a b h => by
    rw [map_pow, map_pow]
    refine pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h) ?_
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (I ^ N)), Ideal.Quotient.eq]
    exact Ideal.pow_le_pow_right (Nat.le_succ N) (zl_pow I l hl u hu N)
  have hex : ∀ s : ℤ_[l], ∃ y : R, ∀ N (k : ℕ), (k : ZMod (l ^ N)) = PadicInt.toZModPow N s →
      Ideal.Quotient.mk (I ^ N) y = Ideal.Quotient.mk (I ^ N) (u ^ k) := fun s => by
    obtain ⟨y, hy⟩ := IsPrecomplete.prec' (I := I) (fun n => (u : R) ^ (PadicInt.toZModPow n s).val)
      (fun {m n} hmn => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
        refine hB _ _ _ ?_
        rw [ZMod.natCast_zmod_val, ZMod.natCast_val, PadicInt.cast_toZModPow _ _ hmn])
    refine ⟨y, fun N k hk => ?_⟩
    have := (hy N).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq] at this
    rw [this]
    exact hB _ _ _ (by rw [ZMod.natCast_zmod_val, hk])
  choose p hp using hex
  let P : Multiplicative ℤ_[l] →* R :=
    { toFun := fun x => p x.toAdd
      map_one' := zl_eq I fun n => by simpa using hp 0 n 0 (by simp)
      map_mul' := fun a b => zl_eq I fun n => by
        rw [toAdd_mul, map_mul (Ideal.Quotient.mk (I ^ n)), hp (_ + _) n _ (ZMod.natCast_zmod_val _), hp a.toAdd n _ (ZMod.natCast_zmod_val _),
          hp b.toAdd n _ (ZMod.natCast_zmod_val _), ← map_mul, ← pow_add]
        exact hB _ _ _ (by simp) }
  refine ⟨P.toHomUnits, fun N => ?_, Units.ext (zl_eq I fun n => ?_)⟩
  · have : (fun g : Multiplicative ℤ_[l] => Ideal.Quotient.mk (I ^ N) ((P.toHomUnits g : Rˣ) : R)) =
        (fun z : ZMod (l ^ N) => Ideal.Quotient.mk (I ^ N) ((u : R) ^ z.val)) ∘
          ((PadicInt.toZModPow N : ℤ_[l] → ZMod (l ^ N)) ∘ Multiplicative.toAdd) :=
      funext fun g => hp _ N _ (ZMod.natCast_zmod_val _)
    rw [this]
    exact ((zl_lc l N).comp_continuous continuous_toAdd).comp _
  · have := hp 1 n 1 (by simp)
    rw [pow_one] at this
    exact this

theorem UpperTheory.V.W.lam_zl :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ι : Type) [Fintype ι] [DecidableEq ι] (u : ι → Rˣ), (∀ i, res O R (u i) = 1) →
      ∃! χ : Multiplicative (ι → ℤ_[l]) →* Rˣ, AdicCont (maximalIdeal R) (fun x => ((χ x : Rˣ) : R)) ∧ ∀ i, χ (Multiplicative.ofAdd (Pi.single i 1)) = u i := by
  intro l _ O _ _ _ R _ _ _ ι _ _ u hu
  have hl : (l : R) ∈ maximalIdeal R := (res_eq_zero_iff O R _).1 (by rw [map_natCast, CharP.cast_eq_zero])
  have hu' : ∀ i, (u i : R) - 1 ∈ maximalIdeal R := fun i =>
    (res_eq_zero_iff O R _).1 (by rw [map_sub, hu, map_one, sub_self])
  choose c hc hc1 using fun i => zl_one l (maximalIdeal R) hl (u i) (hu' i)
  refine existsUnique_of_exists_of_unique ⟨?_, ?_, ?_⟩ ?_
  · exact
      { toFun := fun x => ∏ i, c i (Multiplicative.ofAdd (x.toAdd i))
        map_one' := by simp
        map_mul' := fun a b => by simp [ofAdd_add, Finset.prod_mul_distrib] }
  · intro N
    letI : TopologicalSpace (R ⧸ maximalIdeal R ^ N) := ⊥
    haveI : DiscreteTopology (R ⧸ maximalIdeal R ^ N) := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, map_prod]
    refine continuous_finsetProd _ fun i _ => ?_
    exact (hc i N).continuous.comp (continuous_ofAdd.comp ((continuous_apply i).comp continuous_toAdd))
  · intro i
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [Finset.prod_eq_single i, Pi.single_eq_same, hc1]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, ofAdd_zero, map_one]
    · simp
  · rintro χ χ' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine MonoidHom.ext fun x => Units.ext (zl_eq (maximalIdeal R) fun N => ?_)
    letI : TopologicalSpace (R ⧸ maximalIdeal R ^ N) := ⊥
    haveI : DiscreteTopology (R ⧸ maximalIdeal R ^ N) := ⟨rfl⟩
    have hd : DenseRange (Pi.map fun (_ : ι) => (Nat.cast : ℕ → ℤ_[l])) :=
      DenseRange.piMap fun _ => PadicInt.denseRange_natCast
    have key := hd.equalizer ((h1 N).continuous.comp continuous_ofAdd) ((h1' N).continuous.comp continuous_ofAdd)
      (funext fun n => by
        have e : Multiplicative.ofAdd (Pi.map (fun (_ : ι) => (Nat.cast : ℕ → ℤ_[l])) n) =
            ∏ i, Multiplicative.ofAdd (Pi.single i (1 : ℤ_[l]) : ι → ℤ_[l]) ^ n i := by
          apply Multiplicative.toAdd.injective
          funext j
          simp [toAdd_prod, Finset.sum_apply, Pi.single_apply]
        simp only [Function.comp_apply, e, map_prod, map_pow, h2, h2'])
    exact congrFun key x.toAdd
end

