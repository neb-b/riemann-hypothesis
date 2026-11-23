module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0013
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FoCong
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.foCong :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (j N : ℕ), j ≤ N → fo W - fEl (T.Nq N) W.t.U ∈ maximalIdeal W.R ^ j ∧ m.ρ N (fEl (T.Nq N) W.t.U) = fEl (T.Nq N) (A.A N).U ∧ ∃ c : W.R, fo W - fEl (T.Nq N) W.t.U = (l : W.R) ^ j * c := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m j N hj
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI := IsCoef.char (l := l) (O := O)
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hl : (l : W.R) ∈ maximalIdeal W.R := by
    have hco := (inferInstance : IsCO O W.R).isLocalHom
    intro hu
    rw [← map_natCast (algebraMap O W.R)] at hu
    exact hlO (hco.map_nonunit _ hu)
  set I : Ideal W.R := Ideal.span {(l : W.R) ^ j} with hI
  have hq : ∀ jj, (T.Nq N jj : W.R) - 1 ∈ I := by
    intro jj
    obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp (T.Nq_mod N jj).symm
    have h3 := congrArg (Int.cast : ℤ → W.R) hk
    push_cast at h3
    rw [Ideal.mem_span_singleton]
    refine ⟨(l : W.R) ^ (N - j) * (k : W.R), ?_⟩
    rw [h3, ← pow_mul_pow_sub (l : W.R) hj, mul_assoc]
  have hq' : ∀ jj, Ideal.Quotient.mk I (T.Nq N jj : W.R) = 1 := by
    intro jj
    rw [← map_one (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq.mpr (hq jj)
  have hmod : Ideal.Quotient.mk I (fo W) = Ideal.Quotient.mk I (fEl (T.Nq N) W.t.U) := by
    simp only [fo, fEl, map_prod, map_mul, map_sub, hq', Nat.cast_one, map_one, one_mul]
  have hdiff : fo W - fEl (T.Nq N) W.t.U ∈ I := Ideal.Quotient.eq.mp hmod
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdiff
  refine ⟨?_, ?_, ⟨c, hc⟩⟩
  · rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl j)
  · obtain ⟨-, -, -, hU, -⟩ := m.ρ_maps N
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hU
    simp [fEl, map_prod, hU]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FreeNQuot
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem UpperTheory.V.Pa.Core.freeN_quot {R S M : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (s : S →+* R) (I K : Ideal S) (hIK : I ≤ K) (c : ℕ) (e : M ≃+ (Fin c → S ⧸ I))
    (he : ∀ z x, e (s z • x) = z • e x) :
    ∃ e' : (M ⧸ (K.map s • ⊤ : Submodule R M)) ≃+ (Fin c → S ⧸ K), ∀ a x, e' (s a • x) = a • e' x :=
  _root_.UpperTheory.Reformulated.B.FreeModuleQuotient.freeN_quot s I K hIK c e he

private theorem UpperTheory.V.Pa.Core.freeN_le (l : ℕ) (hl : l.Prime) (R : Type) [CommRing R] [IsLocalRing R]
    (hR : (l : R) ∈ maximalIdeal R) (q n : ℕ) (a : Fin q → ℕ) (k j : ℕ) (ha : ∀ i, j + k ≤ a i) :
    delIdeal l R n a ≤ kjIdeal R (Fin q × Fin n) k j := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨p, rfl⟩
  have h1 := ha p.1
  have h2 : a p.1 - j < l ^ (a p.1 - j) := Nat.lt_pow_self hl.one_lt
  have h := one_add_pow_sub_one_mem (MvPowerSeries (Fin q × Fin n) R) l hl (MvPowerSeries.X p) (a p.1) j k
    (by omega) (by omega)
  refine (sup_le_sup ?_ ?_ : _ ≤ kjIdeal R (Fin q × Fin n) k j) h
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self p)) k
  · rw [Ideal.span_singleton_le_iff_mem]
    have := Ideal.mem_map_of_mem (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) (Ideal.pow_mem_pow hR j)
    rwa [map_pow, map_natCast] at this

theorem UpperTheory.V.Pa.Core.freeN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (k j : ℕ), ∀ᶠ N in (Λ.U : Filter ℕ), ∃ (c : ℕ) (e : (MN m N ⧸ ((kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) k j).map m.s.toRingHom • ⊤ : Submodule W.R (MN m N))) ≃+ (Fin c → Sinf O Unit D T.q n ⧸ kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) k j)), ∀ a x, e (m.s.toRingHom a • x) = a • e x := by
  intro l hl L G0 T Λ n O _ _ _ hO _ r B _ _ _ u J D A W m k j
  have hlm : (l : abelian₂ O Unit D) ∈ maximalIdeal (abelian₂ O Unit D) := by
    intro hu
    have h1 := hu.map ((residue O).comp (MvPowerSeries.constantCoeff : abelian₂ O Unit D →+* O))
    haveI := hO.char
    rw [map_natCast, CharP.cast_eq_zero] at h1
    exact not_isUnit_zero h1
  refine Λ.U_le ((eventually_ge_atTop (j + k)).mono fun N hN => ⟨(A.A N).rk, ?_⟩)
  refine freeN_quot (M := MN m N) m.s.toRingHom _ _
    (freeN_le l hl.out _ hlm T.q n (A.A N).a k j fun i => hN.trans ((A.A N).le_a i)) _ (A.A N).e ?_
  intro z x
  have := (A.A N).e_smul z x
  rw [← m.specializationMap_comp_universalSection N z] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LaDimArith
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem laDim_co (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) : IsCO O K := by
  refine { complete := ?_, isLocalHom := IsLocalHom.of_surjective _ h, res_surj := ?_ }
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · intro x
    obtain ⟨a, rfl⟩ := h x
    exact ⟨a, by simp⟩

private theorem laDim_surj (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (K : Type) [Field K] [Algebra O K] (σ : Type) [Finite σ] (s : σ)
    (g : MvPowerSeries σ O →ₐ[O] PowerSeries K) (h : Function.Surjective (algebraMap O K))
    (hg : g (MvPowerSeries.X s) = PowerSeries.X) : Function.Surjective g := by
  haveI : IsCO O K := laDim_co O K h
  haveI : IsCO O (MvPowerSeries σ O) := co_mvps O O σ
  haveI : IsCO O (PowerSeries K) := co_mvps O K Unit
  refine co_surj O _ _ g (le_trans ?_ le_sup_left)
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_le, Set.singleton_subset_iff, ← hg]
  refine Ideal.mem_map_of_mem _ fun hu => ?_
  have := MvPowerSeries.isUnit_constantCoeff _ hu
  simp at this

private theorem laDim_arith (x : WithBot ℕ∞) (n : ℕ) (h : x + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    x = (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    have h' : y + 1 = ((n : ℕ∞) + 1) := by exact_mod_cast h
    have : y = (n : ℕ∞) := WithTop.add_right_cancel ENat.one_ne_top h'
    rw [this]; rfl

private theorem laDim_gen (R : Type) [CommRing R] [IsRegularLocalRing R] (S : Type) [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (p : Ideal R) (e : (R ⧸ p) ≃+* S) (n : ℕ)
    (hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra R La),
      IsCplAt R p La ∧ IsRegularLocalRing La ∧ ringKrullDim La = (n : WithBot ℕ∞) := by
  haveI : IsDomain (R ⧸ p) := e.toMulEquiv.isDomain _
  haveI hp : p.IsPrime := (Ideal.Quotient.isDomain_iff_prime p).1 inferInstance
  haveI : IsRegularLocalRing (R ⧸ p) := IsRegularLocalRing.of_ringEquiv e.symm
  have hq : ringKrullDim (R ⧸ p) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e, IsDiscreteValuationRing.ringKrullDim_eq_one]
  obtain ⟨h1, h2⟩ := regular_localization_of_regular_quotient R p
  have hc := isCplAt_cplAt R p
  obtain ⟨h3, h4⟩ := IsCplAt.regular _ _ _ hc h1
  refine ⟨CplAt R p, inferInstance, inferInstance, inferInstance, hc, h3, ?_⟩
  rw [h4]
  apply laDim_arith
  rw [hq] at h2
  rw [h2, hdim]

theorem UpperTheory.V.Pa.Core.laDim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (K : Type) [Field K] [Finite K] [Algebra O K] (D : ℕ) (g : abelian₂ O Unit D →ₐ[O] PowerSeries K), Function.Surjective (algebraMap O K) → g (MvPowerSeries.X (.inl ())) = PowerSeries.X → ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra (abelian₂ O Unit D) La), IsCplAt (abelian₂ O Unit D) (RingHom.ker g) La ∧ IsRegularLocalRing La ∧ ringKrullDim La = ((1 + D : ℕ) : WithBot ℕ∞) := by
  intro O _ _ _ _ K _ _ _ D g h hg
  have hs : Function.Surjective g := laDim_surj O K _ _ g h hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hreg, hdim, -⟩ := mvPowerSeries_cotInd O ϖ hϖ (Unit ⊕ Fin D)
  haveI : IsRegularLocalRing (abelian₂ O Unit D) := hreg
  refine laDim_gen (abelian₂ O Unit D) (PowerSeries K) (RingHom.ker g)
    (Ideal.quotientKerAlgEquivOfSurjective hs).toRingEquiv (1 + D) ?_
  rw [hdim, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LamComap
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mem_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {y : R} (hy : y ∈ maximalIdeal R) :
    f y ∈ maximalIdeal R' := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
  exact hy

private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := by
  intro N
  have hle : ∀ x ∈ maximalIdeal R ^ N, Ideal.Quotient.mk (maximalIdeal R' ^ N) (f x) = 0 := by
    intro x hx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hm : maximalIdeal R ≤ Ideal.comap f (maximalIdeal R') := fun y hy => mem_map f hy
    exact Ideal.le_comap_pow f N (Ideal.pow_right_mono hm N hx)
  have hc := (ha N).comp (Ideal.Quotient.lift (maximalIdeal R ^ N)
    ((Ideal.Quotient.mk (maximalIdeal R' ^ N)).comp (f : R →+* R')) hle)
  convert hc using 1
  funext g
  rfl

private theorem map_X_mem {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] {σ : Type} [Finite σ] (f : MvPowerSeries σ R →ₐ[O] R') (a : σ) :
    f (MvPowerSeries.X a) ∈ maximalIdeal R' := by
  haveI : IsCO O (MvPowerSeries σ R) := co_mvps O R σ
  apply mem_map f
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  simp [MvPowerSeries.constantCoeff_X]

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  simp only [GDet.lam, GDet.chi, GDet.comap, MonoidHom.coe_comp, Function.comp_apply,
    MonoidAlgebra.mapRingHom_single, Polynomial.C_1]
  congr 4
  change MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single g 1) = _
  rw [map_sub]
  simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

theorem UpperTheory.V.Pa.Core.tupPi :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) [IsCO O (Spo A)], ∃ t : Tup Λ A (Spo A), t.D = (u.D.comap (Λ.h.p₀.comp (πo0 Λ))).map (algebraMap B (Spo A)) ∧ (t.ψ = fun v i => pushCh (algebraMap B (Spo A)) (u.ψ v i)) ∧ t.s = algebraMap B (Spo A) (A.b.lam (MvPowerSeries.X (.inl ()))) ∧ (t.U = fun j i => Sp.u _ _ j i) ∧ t.y = fun _ _ => 0 := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A _
  let f : B →ₐ[O] Spo A := IsScalarTower.toAlgHom O B (Spo A)
  have hφc : Continuous (Λ.h.p₀.comp (πo0 Λ)) := (Λ.h.p₀_cont).comp Λ.πo0_cont
  refine ⟨⟨(u.D.comap (Λ.h.p₀.comp (πo0 Λ))).map (algebraMap B (Spo A)), ?cont, ?red,
    fun v i => pushCh (algebraMap B (Spo A)) (u.ψ v i), ?psi,
    algebraMap B (Spo A) (A.b.lam (MvPowerSeries.X (.inl ()))), ?smem,
    fun j i => Sp.u _ _ j i, ?umem, fun _ _ => 0, fun _ _ => Ideal.zero_mem _⟩, rfl, rfl, rfl, rfl, rfl⟩
  case cont =>
    intro i
    have h1 : ∀ g, ((u.D.comap (Λ.h.p₀.comp (πo0 Λ))).map (algebraMap B (Spo A))).lam i
        (MonoidAlgebra.single g 1) = f (u.D.lam i (MonoidAlgebra.single ((Λ.h.p₀.comp (πo0 Λ)) g) 1)) := by
      intro g
      have h2 := ((UpperTheory.V.CA.d_gmap (u.D.comap (Λ.h.p₀.comp (πo0 Λ)))).2.2.1 (algebraMap B (Spo A))
        (MonoidAlgebra.single g 1)).2 i
      rw [MonoidAlgebra.mapRingHom_single, map_one] at h2
      rw [h2, lam_comap]
      rfl
    simp only [h1]
    exact adic_map f (fun N => ((u.cont i) N).comp_continuous hφc)
  case red =>
    rw [(UpperTheory.V.CA.d_gmap _).2.1]
    have h3 : (↑(res O (Spo A)) : Spo A →+* ResidueField O).comp (algebraMap B (Spo A)) = ↑(res O B) :=
      RingHom.ext fun x => res_map f x
    rw [h3, ← u.red]
    rfl
  case psi =>
    intro v i
    refine ⟨adic_map f (u.psi v i).cont, fun g => ?_, fun g => ?_⟩
    · show res O (Spo A) (f ↑(u.ψ v i g)) = _
      rw [res_map]
      exact (u.psi v i).red g
    · show f ↑(u.ψ v i g) = _
      rw [(u.psi v i).mu g, AlgHom.commutes]
  case smem =>
    haveI : IsCO O O := IsCO.mk IsCoef.complete ⟨fun a ha => by simpa using ha⟩ (fun x => ⟨x, by simp⟩)
    exact _root_.mem_map f (map_X_mem A.b.lam (Sum.inl ()))
  case umem =>
    intro j i
    have hC : ∀ b : B, (MvPowerSeries.C b : MvPowerSeries (Fin T.q × Fin n) B) =
        algebraMap B (MvPowerSeries (Fin T.q × Fin n) B) b := fun b => by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h4 : Sp.u _ _ j i - algebraMap O (Spo A) (A.ut j i) =
        (Sp.mk _ _).restrictScalars O (MvPowerSeries.X (j, i)) := by
      simp only [Sp.u, map_add (f := _), AlgHom.restrictScalars_apply]
      rw [add_sub_right_comm, sub_eq_zero.mpr, zero_add]
      rw [hC, AlgHom.commutes, ← IsScalarTower.algebraMap_apply O B (Spo A)]
    rw [h4]
    exact map_X_mem _ (j, i)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LamEqOfKer
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_eq_of_ker {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    {x y : E} (h : x - y ∈ D.ker) (i : ℕ) : D.lam i x = D.lam i y := by
  have hchi : D.chi x = D.chi y := by
    have h2 := ((UpperTheory.V.CA.d_ker D (x - y)).2.1.1 h) (Polynomial A) (-1)
      (Polynomial.X ⊗ₜ[A] (1 : E) - 1 ⊗ₜ[A] y)
    unfold Det.chi
    rw [← h2]
    congr 1
    rw [TensorProduct.neg_tmul, TensorProduct.tmul_sub]
    abel
  unfold Det.lam
  rw [hchi]

private theorem sub_mem_ker {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (V : Subgroup G)
    [V.Normal] (hV : ∀ h ∈ V, D.Kills (MonoidAlgebra.single h 1 - 1)) (x : MonoidAlgebra A G) :
    x - MonoidAlgebra.mapDomain (fun q : G ⧸ V => q.out)
      (MonoidAlgebra.mapDomainRingHom A (QuotientGroup.mk' V) x) ∈ D.toDet.ker := by
  have hker : ∀ h ∈ V, MonoidAlgebra.single h (1 : A) - 1 ∈ D.toDet.ker := fun h hh =>
    (UpperTheory.V.CA.d_ker D.toDet _).1.2 ((UpperTheory.V.CA.d_toDet D _).2.2.2.2 (hV h hh))
  rw [MonoidAlgebra.mapDomainRingHom_apply]
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [MonoidAlgebra.mapDomain_add, MonoidAlgebra.mapDomain_add]
    have := D.toDet.ker.add_mem ha hb
    convert this using 1
    abel
  | single g r =>
    rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single]
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V g
    have hv' : (QuotientGroup.mk' V g).out = g * v := hv
    rw [hv']
    have heq : MonoidAlgebra.single g r - MonoidAlgebra.single (g * (v : G)) r
        = -(MonoidAlgebra.single g r * (MonoidAlgebra.single (v : G) (1 : A) - 1)) := by
      rw [mul_sub, mul_one, MonoidAlgebra.single_mul_single, mul_one]
      abel
    rw [heq]
    exact D.toDet.ker.neg_mem (D.toDet.ker.mul_mem_left _ _ (hker _ v.2))

theorem UpperTheory.V.Pa.Core.dSees :
    ∀ (n : ℕ) (R G : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n R G) (I : Ideal R), D.IsCont I → ∀ N : ℕ, ∃ V : OpenNormalSubgroup G, Sees D V.toSubgroup (I ^ N) := by
  intro n R G _ _ _ _ _ _ D I hD N
  obtain ⟨V, hV⟩ := UpperTheory.V.CA.exists_openNormalSubgroup_kills_of_groupDetLaw_isCont D I hD N
  refine ⟨V, ?_⟩
  intro i x y hxy
  set f := Ideal.Quotient.mk (I ^ N)
  set D' := D.map f
  have hcomm : ∀ z : MonoidAlgebra R G,
      MonoidAlgebra.mapDomainRingHom (R ⧸ I ^ N) (QuotientGroup.mk' V.toSubgroup)
          (MonoidAlgebra.mapRingHom G f z) =
        MonoidAlgebra.mapRingHom (G ⧸ V.toSubgroup) f
          (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V.toSubgroup) z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  have key : ∀ z : MonoidAlgebra R G, D'.lam i (MonoidAlgebra.mapRingHom G f z) =
      D'.lam i (MonoidAlgebra.mapDomain (fun q : G ⧸ V.toSubgroup => q.out)
        (MonoidAlgebra.mapDomainRingHom (R ⧸ I ^ N) (QuotientGroup.mk' V.toSubgroup)
          (MonoidAlgebra.mapRingHom G f z))) := by
    intro z
    rw [← (UpperTheory.V.CA.d_toDet D' _).2.1 i, ← (UpperTheory.V.CA.d_toDet D' _).2.1 i]
    exact lam_eq_of_ker D'.toDet (sub_mem_ker D' V.toSubgroup hV _) i
  have h1 := key x
  have h2 := key y
  rw [hcomm x, hxy, ← hcomm y, ← h2] at h1
  rw [((UpperTheory.V.CA.d_gmap D).2.2.1 f x).2 i, ((UpperTheory.V.CA.d_gmap D).2.2.1 f y).2 i] at h1
  exact Ideal.Quotient.eq.1 h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OutOfNil
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem comap_comap_quot {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ii : Ideal R)
    (Q : Ideal (B ⧸ ii.map (algebraMap R B))) :
    (Q.comap (algebraMap (R ⧸ ii) (B ⧸ ii.map (algebraMap R B)))).comap (Ideal.Quotient.mk ii) =
      (Q.comap (Ideal.Quotient.mk (ii.map (algebraMap R B)))).comap (algebraMap R B) := by
  ext x
  rfl

private theorem dim_quot {B : Type} [CommRing B] (I S : Ideal B) (h : I ≤ S.radical) (d : WithBot ℕ∞)
    (hd : ∀ P ∈ S.minimalPrimes, d ≤ ringKrullDim (B ⧸ P)) (P : Ideal (B ⧸ I))
    (hP : P ∈ (S.map (Ideal.Quotient.mk I)).minimalPrimes) : d ≤ ringKrullDim ((B ⧸ I) ⧸ P) := by
  rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker] at hP
  obtain ⟨P', hP', rfl⟩ := hP
  have hIP : I ≤ P' := le_sup_right.trans hP'.1.2
  have hmin : P' ∈ S.minimalPrimes := by
    refine ⟨⟨hP'.1.1, le_sup_left.trans hP'.1.2⟩, ?_⟩
    intro Q hQ hQP
    haveI := hQ.1
    exact hP'.2 ⟨hQ.1, sup_le hQ.2 (h.trans ((Ideal.IsPrime.radical_le_iff hQ.1).mpr hQ.2))⟩ hQP
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I P'), sup_eq_right.mpr hIP]
  exact hd P' hmin

theorem UpperTheory.V.Pa.Core.outOfNil :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing R] (s : MvPowerSeries σ Λ →+* R) (ii ann : Ideal R) (ι : Type) (q : ι → Ideal R) (d : ℕ) (B : ι → Type) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)] [∀ i, Algebra R (B i)] (S : ∀ i, Ideal (B i)), (∀ i, ii ≤ q i) → (∀ i, IsCplAt R (q i) (B i)) → (∀ i, ii ≤ (S i).radical.comap (algebraMap R (B i))) → (∀ i, ∀ P ∈ (S i).minimalPrimes, (d : WithBot ℕ∞) ≤ ringKrullDim (B i ⧸ P)) → (∀ i (Q : Ideal (B i)), Q.IsPrime → ii.map (algebraMap R (B i)) ≤ Q → (∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q) → (S i ≤ Q ↔ ann ≤ Q.comap (algebraMap R (B i)))) → (∀ i i' (Z Q : Ideal (B i)), Z.IsPrime → Q.IsPrime → S i ≤ Z → Z ≤ Q → (∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q) → Q.comap (algebraMap R (B i)) ≤ q i' → ∃ Z' : Ideal (B i'), Z'.IsPrime ∧ S i' ≤ Z' ∧ Z'.comap (algebraMap R (B i')) = Z.comap (algebraMap R (B i))) → Nonempty (PatchedSupportCompletions s ii ann q d) := by
  intro Λ R σ _ _ _ _ s ii ann ι q d B _ _ _ S hq hcpl hrad hdim hfib hmove
  let J : ∀ i, Ideal (B i) := fun i => ii.map (algebraMap R (B i))
  have hJmax : ∀ i, J i ≤ maximalIdeal (B i) := by
    intro i
    rw [Ideal.map_le_iff_le_comap, (hcpl i).comap_eq]
    exact hq i
  have hJne : ∀ i, J i ≠ ⊤ := fun i h => (IsLocalRing.maximalIdeal.isMaximal (B i)).ne_top (top_le_iff.mp (h ▸ hJmax i))
  haveI : ∀ i, Nontrivial (B i ⧸ J i) := fun i => Ideal.Quotient.nontrivial_iff.mpr (hJne i)
  haveI : ∀ i, IsLocalRing (B i ⧸ J i) := fun i => .of_surjective' _ Ideal.Quotient.mk_surjective
  have hker : ∀ i, J i ≤ RingHom.ker (Ideal.Quotient.mk (J i)) := fun i => by rw [Ideal.mk_ker]
  have hcomap : ∀ i (Z : Ideal (B i ⧸ J i)),
      (Z.comap (algebraMap (R ⧸ ii) (B i ⧸ J i))).comap (Ideal.Quotient.mk ii) =
        (Z.comap (Ideal.Quotient.mk (J i))).comap (algebraMap R (B i)) :=
    fun i Z => comap_comap_quot ii Z
  have hJle : ∀ i (Z : Ideal (B i ⧸ J i)), J i ≤ Z.comap (Ideal.Quotient.mk (J i)) := by
    intro i Z x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Z.zero_mem
  have hgen : ∀ i (Q : Ideal (B i ⧸ J i)),
      ((∀ a, algebraMap (R ⧸ ii) (B i ⧸ J i) (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q) ↔
        ∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q.comap (Ideal.Quotient.mk (J i))) := by
    intro i Q
    rfl
  refine ⟨⟨fun i => B i ⧸ J i, fun i => ?_, fun i => (S i).map (Ideal.Quotient.mk (J i)), fun i => ?_,
    fun i Q hQ hgQ => ?_, fun i i' Z Q hZ hQ hSZ hZQ hgQ hQq => ?_⟩⟩
  · exact IsCplAt.quotient R (q i) (B i) (R ⧸ ii) ((q i).map (Ideal.Quotient.mk ii)) (B i ⧸ J i) (hcpl i)
      Ideal.Quotient.mk_surjective
      (by
        show Ideal.comap (Ideal.Quotient.mk ii) _ = _
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
          Ideal.mk_ker]
        exact sup_eq_left.mpr (hq i))
      Ideal.Quotient.mk_surjective
      (by
        show RingHom.ker (Ideal.Quotient.mk (J i)) = Ideal.map _ (RingHom.ker (Ideal.Quotient.mk ii))
        rw [Ideal.mk_ker, Ideal.mk_ker])
  · intro P hP
    exact dim_quot (J i) (S i) (Ideal.map_le_iff_le_comap.mpr (hrad i)) d (hdim i) P hP
  · haveI := hQ
    rw [Ideal.map_le_iff_le_comap, hcomap]
    exact hfib i _ (Ideal.comap_isPrime _ Q) (hJle i Q) ((hgen i Q).mp hgQ)
  · haveI := hZ
    haveI := hQ
    rw [hcomap] at hQq
    obtain ⟨Z'', hZ''p, hSZ'', hZ''⟩ := hmove i i' (Z.comap (Ideal.Quotient.mk (J i)))
      (Q.comap (Ideal.Quotient.mk (J i))) (Ideal.comap_isPrime _ Z) (Ideal.comap_isPrime _ Q)
      (Ideal.map_le_iff_le_comap.mp hSZ) (Ideal.comap_mono hZQ) ((hgen i Q).mp hgQ) hQq
    have hiiZ : ii ≤ Z''.comap (algebraMap R (B i')) := by
      rw [hZ'', ← Ideal.map_le_iff_le_comap]
      exact hJle i Z
    have hJZ : J i' ≤ Z'' := Ideal.map_le_iff_le_comap.mpr hiiZ
    have hkZ : RingHom.ker (Ideal.Quotient.mk (J i')) ≤ Z'' := by rw [Ideal.mk_ker]; exact hJZ
    refine ⟨Z''.map (Ideal.Quotient.mk (J i')), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkZ,
      Ideal.map_mono hSZ'', ?_⟩
    apply Ideal.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := ii))
    rw [hcomap, hcomap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkZ, hZ'']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedModuleAnnihilatorLeComapIffIdealLe
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem ann_baseChange_le_iff (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (M : Type) [AddCommGroup M]
    [Module B M] [Module.Finite B M] (P : Ideal S) (hP : P.IsPrime) :
    Module.annihilator S (S ⊗[B] M) ≤ P ↔ Module.annihilator B M ≤ P.comap (algebraMap B S) := by
  have h := UpperTheory.V.AlgebraTools.mem_support_baseChange B S M ⟨P, hP⟩
  rw [Module.mem_support_iff_of_finite, Module.mem_support_iff_of_finite] at h
  exact h

theorem UpperTheory.V.Pa.Core.patchedModule_annihilator_le_comap_iff_ideal_le :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Function.Surjective m.π → ∀ P : Ideal (Spo A), P.IsPrime → (Module.annihilator W.R (X0 m) ≤ P.comap m.π ↔ J ≤ P.comap (algebraMap B (Spo A))) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hπ P hP
  have hfin : Module.Finite B A.b.M := by
    letI : Algebra (abelian₂ O Unit D) B := A.b.lam.toRingHom.toAlgebra
    haveI : IsScalarTower (abelian₂ O Unit D) B A.b.M :=
      IsScalarTower.of_algebraMap_smul fun a x => (A.b.smul_lam a x).symm
    haveI := A.b.fin
    exact Module.Finite.of_restrictScalars_finite (abelian₂ O Unit D) B A.b.M
  have h1 : Module.annihilator W.R (X0 m) =
      (Module.annihilator (Spo A) (Spo A ⊗[B] A.b.M)).comap m.π := by
    ext a
    rw [Ideal.mem_comap, Module.mem_annihilator, Module.mem_annihilator]
    exact Iff.rfl
  rw [h1, Ideal.comap_le_comap_iff_of_surjective m.π hπ, ann_baseChange_le_iff B (Spo A) A.b.M P hP]
  exact A.b.supp _ (Ideal.comap_isPrime _ P)
end

