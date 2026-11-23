module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedLamConjTwistApproxAnnihilated
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem ker_open {l : ℕ} [Fact l.Prime] {Γ S : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CommRing S] (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (φ : ℤ_[l] →+* S) (j : ℕ) (hφ : φ ((l : ℤ_[l]) ^ j) = 0) :
    IsOpen ((pushCh φ ε).ker : Set Γ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hc : Continuous fun g => ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ :=
    ((Units.continuous_val.comp hε).sub continuous_const).norm
  have hp : (0 : ℝ) < (l : ℝ) ^ (-(j : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  have ho : IsOpen {g | ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < (l : ℝ) ^ (-(j : ℤ))} := isOpen_lt hc continuous_const
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using hp)) fun g hg => ?_
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ j).1 (le_of_lt hg)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : φ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    have := congrArg φ hc
    rw [map_mul, hφ, mul_zero, map_sub, map_one] at this
    exact (sub_eq_zero.1 this.symm)
  exact Units.ext h2

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (h : H) (a : A) :
    (D.comap φ).lam i (MonoidAlgebra.single h a) = D.lam i (MonoidAlgebra.single (φ h) a) := by
  have : (D.comap φ).chi (MonoidAlgebra.single h a) = D.chi (MonoidAlgebra.single (φ h) a) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  simp only [GDet.lam, this]

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (h : G) (a : A) :
    f (D.lam i (MonoidAlgebra.single h a)) = (D.map f).lam i (MonoidAlgebra.single h (f a)) := by
  rw [← ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single h a)).2 i, MonoidAlgebra.mapRingHom_single]

theorem UpperTheory.V.Pa.Core.patched_lam_conj_twist_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (i : ℕ) (g g' : Ph0 Λ), (g' : Λ.Ph) = Λ.ct * g * Λ.ct⁻¹ → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, (W.t.D.lam i (MonoidAlgebra.single g'⁻¹ ((Λ.G.frame.eps O W.R (πo0 Λ g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R)) - W.t.D.lam i (MonoidAlgebra.single g 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ hO _ r B _ _ _ u J D A W m _ i g g' hg j
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI := hO.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hlR : (l : W.R) ∈ maximalIdeal W.R := by
    have := map_nonunit (algebraMap O W.R) _ hlO
    rwa [map_natCast] at this
  let q := Ideal.Quotient.mk (maximalIdeal W.R ^ j)
  let φ : ℤ_[l] →+* W.R ⧸ maximalIdeal W.R ^ j := q.comp ((algebraMap O W.R).comp (algebraMap ℤ_[l] O))
  have hφ : φ ((l : ℤ_[l]) ^ j) = 0 := by
    rw [map_pow, map_natCast, ← map_natCast q, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hlR j)
  let V : OpenNormalSubgroup G0.Γ :=
    { toSubgroup := (pushCh φ G0.ε).ker
      isOpen' := ker_open G0.ε G0.ε_cont φ j hφ
      isNormal' := MonoidHom.normal_ker _ }
  refine (Λ.p_lim V).mono fun N hN => ?_
  have h1 : pushCh φ G0.ε ((T.h N).p (Λ.π N g) * (Λ.h.p (Λ.πo g))⁻¹) = 1 := hN g
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have h2 : Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j) ((T.GN N).frame.eps O W.R (πN0 Λ N g)) =
      Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j) (Λ.G.frame.eps O W.R (πo0 Λ g)) := by
    have h3 := congrArg Units.val h1
    change φ (G0.ε _ : ℤ_[l]ˣ) = φ (G0.ε _ : ℤ_[l]ˣ) at h3
    rw [(T.h N).ε, Λ.h.ε] at h3
    exact Units.ext h3
  refine ⟨W.t.D.lam i (MonoidAlgebra.single g'⁻¹
      (((T.GN N).frame.eps O W.R (πN0 Λ N g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R)) -
      W.t.D.lam i (MonoidAlgebra.single g 1), ?_, Or.inl ?_⟩
  · rw [sub_sub_sub_cancel_right, ← Ideal.Quotient.eq]
    change q _ = q _
    rw [lam_map, lam_map]
    have h4 := congrArg (fun z : (W.R ⧸ maximalIdeal W.R ^ j)ˣ => ((z ^ (1 - (n : ℤ)) : _ˣ) : W.R ⧸ maximalIdeal W.R ^ j)) h2
    simp only [← map_zpow (Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j))] at h4
    exact congrArg (fun z => (W.t.D.map q).lam i (MonoidAlgebra.single g'⁻¹ z)) h4.symm
  · rw [map_sub, sub_eq_zero]
    change (m.ρ N).toRingHom _ = (m.ρ N).toRingHom _
    rw [lam_map, lam_map, (m.ρ_maps N).1, lam_comap, lam_comap, map_one, ← (A.A N).p.P i (πN0 Λ N g)]
    have e1 : πN0 Λ N g' = (T.GN N).frame.conj (πN0 Λ N g) := Subtype.ext (by
      change Λ.π N g' = (T.GN N).c * Λ.π N g * (T.GN N).c⁻¹
      rw [hg, map_mul, map_mul, map_inv, Λ.ct_N])
    have e2 : Units.map ((m.ρ N).toRingHom : W.R →* (A.A N).R) ((T.GN N).frame.eps O W.R (πN0 Λ N g)) =
        (T.GN N).frame.eps O (A.A N).R (πN0 Λ N g) := Units.ext ((m.ρ N).commutes _)
    have e3 : (m.ρ N).toRingHom (((T.GN N).frame.eps O W.R (πN0 Λ N g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R) =
        (((T.GN N).frame.eps O (A.A N).R (πN0 Λ N g) ^ (1 - (n : ℤ)) : (A.A N).Rˣ) : (A.A N).R) := by
      rw [← e2, ← map_zpow (Units.map ((m.ρ N).toRingHom : W.R →* (A.A N).R))]
      rfl
    rw [e3, map_inv, e1]
    congr 1
    simp [GFrame.star, GFrame.starOp]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmFib
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.pmFib :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Fintype σ] (y : σ → R) (f : R) (ii : Ideal R) (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X] (P : PMod y f ii X) (B : Type) [CommRing B] [Algebra P.BB B] (Q : Ideal B), Q.IsPrime → (∀ a, algebraMap P.BB B (algebraMap R P.BB (y a)) ∈ Q) → (Module.annihilator B (B ⊗[P.BB] P.MM) ≤ Q ↔ Module.annihilator R X ≤ (Q.comap (algebraMap P.BB B)).comap (algebraMap R P.BB)) := by
  intro R σ _ _ _ y f ii X _ _ _ P B _ _ Q hQ hy
  haveI := P.fin
  let Qp : PrimeSpectrum B := ⟨Q, hQ⟩
  let q := PrimeSpectrum.comap (algebraMap P.BB B) Qp
  have h1 := Module.mem_support_iff_of_finite (R := B) (M := B ⊗[P.BB] P.MM) (p := Qp)
  have h2 := mem_support_baseChange P.BB B P.MM Qp
  have h3 := Module.support_quotient (R := P.BB) (M := P.MM)
    (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)))
  have h4 := P.fib.support_eq
  have h5 := mem_support_baseChange R P.BB X q
  have h6 := Module.mem_support_iff_of_finite (R := R) (M := X) (p := PrimeSpectrum.comap (algebraMap R P.BB) q)
  have hz : q ∈ PrimeSpectrum.zeroLocus (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)) : Set P.BB) := by
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact hy a
  calc Module.annihilator B (B ⊗[P.BB] P.MM) ≤ Q ↔ Qp ∈ Module.support B (B ⊗[P.BB] P.MM) := h1.symm
    _ ↔ q ∈ Module.support P.BB P.MM := h2
    _ ↔ q ∈ Module.support P.BB (P.MM ⧸ (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)) • ⊤ : Submodule P.BB P.MM)) := by
      rw [h3]
      exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩
    _ ↔ q ∈ Module.support P.BB (P.BB ⊗[R] X) := by rw [h4]
    _ ↔ PrimeSpectrum.comap (algebraMap R P.BB) q ∈ Module.support R X := h5
    _ ↔ _ := h6
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmMove
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.pmMove :
    ∀ (BB MM B B' : Type) [CommRing BB] [IsNoetherianRing BB] [AddCommGroup MM] [Module BB MM] [Module.Finite BB MM] [CommRing B] [Algebra BB B] [CommRing B'] [IsLocalRing B'] [Algebra BB B'] (p' : Ideal BB) (Z : Ideal B), IsCplAt BB p' B' → Z.IsPrime → Module.annihilator B (B ⊗[BB] MM) ≤ Z → Z.comap (algebraMap BB B) ≤ p' → ∃ Z' : Ideal B', Z'.IsPrime ∧ Module.annihilator B' (B' ⊗[BB] MM) ≤ Z' ∧ Z'.comap (algebraMap BB B') = Z.comap (algebraMap BB B) := by
  intro BB MM B B' _ _ _ _ _ _ _ _ _ _ p' Z hB' hZ hann hle
  haveI := hZ
  obtain ⟨Q, hQ, hQc⟩ := (IsCplAt.exists_prime_over BB p' B' hB').1 _ (Ideal.IsPrime.comap _) hle
  refine ⟨Q, hQ, ?_, hQc⟩
  let zP : PrimeSpectrum B := ⟨Z, hZ⟩
  let qP : PrimeSpectrum B' := ⟨Q, hQ⟩
  have hz : zP ∈ Module.support B (B ⊗[BB] MM) := Module.mem_support_iff_of_finite.mpr hann
  have hz' := (mem_support_baseChange BB B MM zP).mp hz
  have heq : PrimeSpectrum.comap (algebraMap BB B') qP = PrimeSpectrum.comap (algebraMap BB B) zP :=
    PrimeSpectrum.ext hQc
  have hq : qP ∈ Module.support B' (B' ⊗[BB] MM) := by
    rw [mem_support_baseChange, heq]
    exact hz'
  exact Module.mem_support_iff_of_finite.mp hq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ResPull
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem repAlg_comp {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G)
    (χ : Fin n → G →* Aˣ) (B : Type) [CommRing B] [Algebra A B] (y : MonoidAlgebra B H) :
    GDet.repAlg (diagRep fun i => (χ i).comp φ) B y =
      GDet.repAlg (diagRep χ) B (MonoidAlgebra.mapDomainRingHom B φ y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg, diagRep]

private theorem star_map {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (h : G.Hom G') (n : ℕ)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B : Type) [CommRing B] [Algebra O B] (y : MonoidAlgebra B G.G₀) :
    MonoidAlgebra.mapDomainRingHom B h.p₀ (G.frame.star O B n y) =
      G'.frame.star O B n (MonoidAlgebra.mapDomainRingHom B h.p₀ y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add a b ha hb =>
    simp only [GFrame.star] at ha hb
    simp only [GFrame.star, map_add (f := _), MulOpposite.unop_add, ha, hb]
  | single g r =>
    simp [GFrame.star, GFrame.starOp, ← h.p₀_conj, h.eps_p₀]

theorem UpperTheory.V.Pa.Core.resPull :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (h : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G'.frame O n), ∃ r' : Resid G.frame O n, Glob.Compat h r' r := by
  intro l _ L G G' h n O _ _ _ r
  refine ⟨⟨fun i => (r.chib i).comp h.p₀, fun i => (r.chib_open i).preimage h.p₀_cont, ?_, ?_,
    r.psib, r.psib_open, r.th, r.th_comm⟩, fun _ => rfl, rfl, rfl⟩
  · intro i j hij
    apply r.chib_inj
    ext g
    obtain ⟨g, rfl⟩ := h.p₀_surj g
    exact congrArg Units.val (DFunLike.congr_fun hij g)
  · intro B _ _ _ _ y
    have := r.polar B (MonoidAlgebra.mapDomainRingHom B h.p₀ y)
    rw [← star_map] at this
    change (GDet.repAlg _ B _).det = (GDet.repAlg _ B _).det
    rw [repAlg_comp, repAlg_comp]
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SinfExt
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.sinfExt :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (D q n : ℕ) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (a : Unit ⊕ Fin D → R) (y : Fin q × Fin n → R), (∀ k, a k ∈ maximalIdeal R) → (∀ p, y p ∈ maximalIdeal R) → ∃! s : Sinf O Unit D q n →ₐ[O] R, (∀ k, s (MvPowerSeries.C (MvPowerSeries.X k)) = a k) ∧ ∀ p, s (MvPowerSeries.X p) = y p := by
  intro O _ _ _ _ D q n R _ _ _ a y ha hy
  haveI hO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun x hx => by simpa using hx⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hL : IsCO O (abelian₂ O Unit D) := co_mvps O O (Unit ⊕ Fin D)
  obtain ⟨F1, ⟨hF1C, hF1X⟩, hF1u⟩ := co_ev O O R (Unit ⊕ Fin D) (Algebra.ofId O R) a ha
  obtain ⟨F2, ⟨hF2C, hF2X⟩, hF2u⟩ := co_ev O (abelian₂ O Unit D) R (Fin q × Fin n) F1 y hy
  refine ⟨F2, ⟨fun k => by rw [hF2C, hF1X], hF2X⟩, ?_⟩
  rintro s ⟨hsC, hsX⟩
  let G : abelian₂ O Unit D →ₐ[O] R :=
    s.comp (IsScalarTower.toAlgHom O (abelian₂ O Unit D) (Sinf O Unit D q n))
  have hGapp : ∀ x, G x = s (MvPowerSeries.C x) := by
    intro x
    simp [G, MvPowerSeries.algebraMap_apply]
  have hG : G = F1 := by
    apply hF1u G
    refine ⟨fun x => ?_, fun k => ?_⟩
    · have h1 : (MvPowerSeries.C x : abelian₂ O Unit D) = algebraMap O (abelian₂ O Unit D) x := by
        simp [MvPowerSeries.algebraMap_apply]
      rw [h1, G.commutes]
      rfl
    · rw [hGapp, hsC k]
  apply hF2u s
  refine ⟨fun x => ?_, hsX⟩
  rw [← hG, hGapp]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpCong
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] {A S S' : Type} [CommRing A] [CommRing S] [CommRing S']
  [Algebra R A] [Algebra R S] [Algebra R S'] (I a : Ideal R) (M : Type) [AddCommGroup M] [Module R M]

private theorem UpperTheory.V.Pa.Core.spCong_killI (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (s : S)
    (hs : s ∈ I.map (algebraMap R S)) (w : S ⊗[R] M) :
    s • w ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)) := by
  have h1 : ∀ m ∈ (a • ⊤ : Submodule R M), ∀ t : S,
      t ⊗ₜ[R] m ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)) := by
    intro m hm t
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr m _
      rw [TensorProduct.tmul_smul, ← algebraMap_smul S r]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy
  have h2 : ∀ i ∈ I, ∀ w : S ⊗[R] M,
      algebraMap R S i • w ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)) := by
    intro i hi w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul t m =>
      rw [algebraMap_smul, ← TensorProduct.tmul_smul]
      exact h1 _ (hI (Submodule.smul_mem_smul hi Submodule.mem_top)) t
    | add x y hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact h2 i hi w
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_smul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, mul_smul]
    exact Submodule.smul_mem _ _ hx

private theorem UpperTheory.V.Pa.Core.spCong_map (f : A →ₐ[R] S) (J : Ideal R) :
    (J.map (algebraMap R A)).map (f : A →+* S) = J.map (algebraMap R S) := by
  rw [Ideal.map_map, AlgHom.comp_algebraMap]

private theorem UpperTheory.V.Pa.Core.spCong_kill (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (f : A →ₐ[R] S) (z : A)
    (hz : z ∈ RingHom.ker f ⊔ I.map (algebraMap R A))
    (x : (S ⊗[R] M) ⧸ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) : f z • x = 0 := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine UpperTheory.V.Pa.Core.spCong_killI I a M hI _ ?_ w
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 hz
  rw [map_add (f := _), (RingHom.mem_ker).1 hb, zero_add, ← UpperTheory.V.Pa.Core.spCong_map f I]
  exact Ideal.mem_map_of_mem (f : A →+* S) hc

private theorem UpperTheory.V.Pa.Core.spCong_smul (f : A →ₐ[R] S) (z : A) (x : A ⊗[R] M) :
    f.toLinearMap.rTensor M (z • x) = f z • f.toLinearMap.rTensor M x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

private theorem UpperTheory.V.Pa.Core.spCong_ker (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (f : A →ₐ[R] S)
    (f' : A →ₐ[R] S') (hf : Function.Surjective f)
    (hk : RingHom.ker f ≤ RingHom.ker f' ⊔ I.map (algebraMap R A)) (x : A ⊗[R] M)
    (hx : f.toLinearMap.rTensor M x ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) :
    f'.toLinearMap.rTensor M x ∈ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M)) := by
  have hF : Function.Surjective (f.toLinearMap.rTensor M) := LinearMap.rTensor_surjective M hf
  have h1 : ∀ y ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)), ∃ x, f.toLinearMap.rTensor M x = y ∧
      f'.toLinearMap.rTensor M x ∈ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M)) := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro s hs w _
      rw [← UpperTheory.V.Pa.Core.spCong_map f a] at hs
      obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective (f : A →+* S) hf).1 hs
      obtain ⟨x, rfl⟩ := hF w
      refine ⟨z • x, UpperTheory.V.Pa.Core.spCong_smul M f z x, ?_⟩
      rw [UpperTheory.V.Pa.Core.spCong_smul]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [← UpperTheory.V.Pa.Core.spCong_map f' a]
      exact Ideal.mem_map_of_mem (f' : A →+* S') hz
    · rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
      exact ⟨x + y, map_add _ _ _, by rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy⟩
  have h2 : ∀ w : (LinearMap.ker f.toLinearMap) ⊗[R] M,
      f'.toLinearMap.rTensor M ((LinearMap.ker f.toLinearMap).subtype.rTensor M w) ∈
        (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M)) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul t m =>
      have h := UpperTheory.V.Pa.Core.spCong_kill I a M hI f' t (hk t.2) (Submodule.Quotient.mk (1 ⊗ₜ[R] m))
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      simpa [TensorProduct.smul_tmul'] using h
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  obtain ⟨x', hx', hm⟩ := h1 _ hx
  have hex := rTensor_exact M (LinearMap.exact_subtype_ker_map f.toLinearMap) hf
  obtain ⟨w, hw⟩ := (hex (x - x')).1 (by rw [map_sub, hx', sub_self])
  have h3 := h2 w
  rw [hw, map_sub] at h3
  simpa using Submodule.add_mem _ h3 hm

private theorem UpperTheory.V.Pa.Core.spCong_gen (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (f : A →ₐ[R] S)
    (f' : A →ₐ[R] S') (hf : Function.Surjective f) (hf' : Function.Surjective f')
    (hk : RingHom.ker f ≤ RingHom.ker f' ⊔ I.map (algebraMap R A))
    (hk' : RingHom.ker f' ≤ RingHom.ker f ⊔ I.map (algebraMap R A)) :
    ∃ κ : ((S ⊗[R] M) ⧸ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) ≃+
      ((S' ⊗[R] M) ⧸ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M))),
      ∀ z x, κ (f z • x) = f' z • κ x := by
  let φ : A ⊗[R] M →+ ((S ⊗[R] M) ⧸ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) :=
    (Submodule.mkQ _).toAddMonoidHom.comp (f.toLinearMap.rTensor M).toAddMonoidHom
  let φ' : A ⊗[R] M →+ ((S' ⊗[R] M) ⧸ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M))) :=
    (Submodule.mkQ _).toAddMonoidHom.comp (f'.toLinearMap.rTensor M).toAddMonoidHom
  have e : ∀ x, φ x = Submodule.Quotient.mk (f.toLinearMap.rTensor M x) := fun _ => rfl
  have e' : ∀ x, φ' x = Submodule.Quotient.mk (f'.toLinearMap.rTensor M x) := fun _ => rfl
  have hφ : Function.Surjective φ :=
    (Submodule.Quotient.mk_surjective _).comp (LinearMap.rTensor_surjective M (g := f.toLinearMap) hf)
  have hφ' : Function.Surjective φ' :=
    (Submodule.Quotient.mk_surjective _).comp (LinearMap.rTensor_surjective M (g := f'.toLinearMap) hf')
  have hker : φ.ker = φ'.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, e, e', Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨UpperTheory.V.Pa.Core.spCong_ker I a M hI f f' hf hk x, UpperTheory.V.Pa.Core.spCong_ker I a M hI f' f hf' hk' x⟩
  let κ := ((QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq hker)).trans (QuotientAddGroup.quotientKerEquivOfSurjective φ' hφ')
  have hκ : ∀ x, κ (φ x) = φ' x := by
    intro x
    have : (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x) = QuotientAddGroup.mk x := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    simp only [κ, AddEquiv.trans_apply, this]
    rfl
  refine ⟨κ, fun z x => ?_⟩
  obtain ⟨x, rfl⟩ := hφ x
  have h1 : f z • φ x = φ (z • x) := by
    rw [e, e, UpperTheory.V.Pa.Core.spCong_smul, Submodule.Quotient.mk_smul]
  rw [h1, hκ, hκ, e', e', UpperTheory.V.Pa.Core.spCong_smul, Submodule.Quotient.mk_smul]

private theorem UpperTheory.V.Pa.Core.spCong_ideal {q n : ℕ} (P P' : Fin q → Polynomial R) (ut : Fin q → Fin n → R)
    (h : ∀ j k, (P' j).coeff k - (P j).coeff k ∈ I) :
    spIdeal P ut ≤ spIdeal P' ut ⊔ I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) := by
  unfold spIdeal
  rw [Ideal.span_le]
  rintro _ ⟨j, k, rfl⟩
  refine Submodule.mem_sup.2 ⟨_, Ideal.subset_span ⟨j, k, rfl⟩, _, Ideal.mem_map_of_mem _ (h j k), ?_⟩
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map, map_sub]
  ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.Core.spCong :
    ∀ (R : Type) [CommRing R] (q n : ℕ) (P P' : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (I a : Ideal R) (M : Type) [AddCommGroup M] [Module R M], (∀ j k, (P j).coeff k - (P' j).coeff k ∈ I) → (I • ⊤ : Submodule R M) ≤ a • ⊤ → ∃ κ : ((Sp P ut ⊗[R] M) ⧸ (a.map (algebraMap R (Sp P ut)) • ⊤ : Submodule (Sp P ut) (Sp P ut ⊗[R] M))) ≃+ ((Sp P' ut ⊗[R] M) ⧸ (a.map (algebraMap R (Sp P' ut)) • ⊤ : Submodule (Sp P' ut) (Sp P' ut ⊗[R] M))), (∀ z x, κ (Sp.mk P ut z • x) = Sp.mk P' ut z • κ x) ∧ ∀ z ∈ spIdeal P ut ⊔ I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R), ∀ x : (Sp P ut ⊗[R] M) ⧸ (a.map (algebraMap R (Sp P ut)) • ⊤ : Submodule (Sp P ut) (Sp P ut ⊗[R] M)), Sp.mk P ut z • x = 0 := by
  intro R _ q n P P' ut I a M _ _ h hI
  have hk : ∀ Q : Fin q → Polynomial R, RingHom.ker (Sp.mk Q ut) = spIdeal Q ut := fun Q =>
    Ideal.Quotient.mkₐ_ker R (spIdeal Q ut)
  have hs : ∀ Q : Fin q → Polynomial R, Function.Surjective (Sp.mk Q ut) := fun Q =>
    Ideal.Quotient.mkₐ_surjective R (spIdeal Q ut)
  have hC : (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) =
      algebraMap R (MvPowerSeries (Fin q × Fin n) R) := by
    ext1 r
    simp [MvPowerSeries.algebraMap_apply]
  have h' : ∀ j k, (P' j).coeff k - (P j).coeff k ∈ I := fun j k => by
    rw [← neg_sub]
    exact I.neg_mem (h j k)
  obtain ⟨κ, hκ⟩ := UpperTheory.V.Pa.Core.spCong_gen I a M hI (Sp.mk P ut) (Sp.mk P' ut) (hs P) (hs P')
    (by rw [hk, hk, ← hC]; exact UpperTheory.V.Pa.Core.spCong_ideal I P P' ut h')
    (by rw [hk, hk, ← hC]; exact UpperTheory.V.Pa.Core.spCong_ideal I P' P ut h)
  refine ⟨κ, hκ, fun z hz x => UpperTheory.V.Pa.Core.spCong_kill I a M hI _ z ?_ x⟩
  rw [hk, ← hC]
  exact hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.spRoots :
    ∀ (R : Type) [CommRing R] (q n : ℕ) (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (j : Fin q), (∏ i, (Polynomial.X - Polynomial.C (Sp.u P ut j i))) = (P j).map (algebraMap R (Sp P ut)) ∧ ∀ i, Sp.u P ut j i - algebraMap R (Sp P ut) (ut j i) = Sp.mk P ut (MvPowerSeries.X (j, i)) := by
  intro R _ q n P ut j
  have hC : ∀ a : R, Sp.mk P ut (MvPowerSeries.C a) = algebraMap R (Sp P ut) a := fun a =>
    (Sp.mk P ut).commutes a
  refine ⟨?_, fun i => ?_⟩
  · have h1 : (∏ i, (Polynomial.X - Polynomial.C (Sp.u P ut j i))) =
        (∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i) : MvPowerSeries (Fin q × Fin n) R))).map (Sp.mk P ut).toRingHom := by
      rw [Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
    rw [h1]
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_map, ← hC]
    refine (Ideal.Quotient.eq (I := spIdeal P ut)).2 ?_
    exact Ideal.subset_span ⟨j, k, by rw [Polynomial.coeff_sub, Polynomial.coeff_map]⟩
  · rw [Sp.u, map_add (f := _), hC, add_sub_cancel_left]
end

