module

public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0012
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.RealExtOfExact

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMem
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03.K8

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem mem_holds [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (hP4 : LevelMapHodgeFiltration W)
    (hSat : Sat W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hfree : (latOf C).Free c)
    (hζ : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    {ell : ℕ} (hell : ell ≤ n) {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c} (m : ℕ)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (hfilt : ∀ s < ell, IsFilt (FilD W T c s)) (ϖ : O)
    (hcompl : ∀ s < ell, ∀ (k : ℕ) (a : PowerSeries O), PowerSeries.X ^ k ∣ rhoL hR c s a →
      ∃ (N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * a = (baseIdOf hR).Bs.p s ^ k * z)
    (hϖ : ∃ (N : ℕ) (u : O), ((PD.p : ℕ) : O) ^ N = ϖ * u)
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam)
    (f' : PowerSeries O) (kind : ℕ → Kind) (b : ℕ → ℕ) (η : ℕ) :
    (lvData Hy f' kind b η).Mem := by
  intro x
  have hκE : κ = ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ (H s + m) := by
    rw [hκ, Formalism.ExponentWindows.abelian₂, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => (pow_add _ _ _).symm
  have hloc : ∀ s (hs : s < ell), (lvData Hy f' kind b η).loc s x ∈ (lvData Hy f' kind b η).Nl s ↔
      Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) •
        expN Lb s T c ⟨C.t c (κ • (x : C.V)), Hy.kap x x.2⟩ ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) := by
    intro s hs
    change prL s (locM Lb C Hy.delta ell _ κ Hy.kap Hy.expSemi Hy.locInv x) ∈ Xi _ _ ↔ _
    rw [prL_of_lt s hs]
    rfl
  constructor
  · intro hx s hs
    rw [hloc s hs]
    have hm : (baseIdOf hR).d κ • ((⟨C.t c x, hx⟩ : ↥(W.N T)) : W.DD T) ∈ W.N T := by
      have h0 := Hy.kap x x.2
      change C.t c (κ • (x : C.V)) ∈ W.N T at h0
      rwa [C.t_smul] at h0
    have e1 : (⟨C.t c (κ • (x : C.V)), Hy.kap x x.2⟩ : ↥(W.N T)) = ⟨(baseIdOf hR).d κ • C.t c x, hm⟩ :=
      Subtype.ext (C.t_smul c κ x)
    rw [e1, Hy.expSemi s κ ⟨C.t c x, hx⟩ hm, smul_smul]
    by_cases hu : IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ))
    · rw [Ring.inverse_mul_cancel _ hu, one_smul]
      exact expN_mem_xi hP4 hcrys hLb s _
    · rw [Ring.inverse_non_unit _ hu, zero_mul, zero_smul]
      exact zero_mem _
  · intro h
    have hy : κ • (x : C.V) ∈ (latOf C).N c := Hy.kap x x.2
    have hdet : ∀ s < ell, ∃ y' ∈ (latOf C).N c,
        κ • (x : C.V) = (baseIdOf hR).Bs.p s ^ (H s + m) • y' := by
      intro s hs
      have h1 : Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s)
          (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ (H s' + m)))) •
          expN Lb s T c ⟨C.t c (κ • (x : C.V)), hy⟩ ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) := by
        rw [← hκE]
        exact (hloc s hs).1 (h s hs)
      exact detect hP4 hSat hcrys hLb hmod hP3 hfree ϖ ell hcompl hϖ s hs (hfilt s hs) (H s + m) _ hy
        ((levelCond_iff ell hk1b hunits (fun s' => H s' + m) s hs _ hy Hy.filAnti).1 h1)
    obtain ⟨y', hy', hyy⟩ := combine hSat hcrys ell (fun s' => H s' + m) _ hy hdet
    have hp0 : ∀ s < ell, (baseIdOf hR).Bs.p s ≠ 0 := by
      intro s hs h0
      obtain ⟨ζ, hζ⟩ := hζ
      have hdvd : PD.p ^ (s + 1) ∣ PD.p ^ n := pow_dvd_pow _ (by omega)
      have hprim : IsPrimitiveRoot (ζ ^ (PD.p ^ n / PD.p ^ (s + 1))) (PD.p ^ (s + 1)) := by
        have := hζ.pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (pow_pos PD.hp.pos _) hdvd)
          (pow_pos PD.hp.pos _)).ne' (Nat.div_dvd_of_dvd hdvd)
        rwa [Nat.div_div_self hdvd (pow_pos PD.hp.pos _).ne'] at this
      have : Nonempty (Rs LL PD.p s) :=
        ⟨⟨_, (mem_primitiveRoots (pow_pos PD.hp.pos _)).2 hprim⟩⟩
      obtain ⟨ε, hε⟩ := hk1b s hs
      rw [h0, map_zero] at hε
      exact PowerSeries.X_ne_zero ((Units.mul_right_eq_zero ε).1 hε.symm)
    have hκ0 : κ ≠ 0 := by
      rw [hκE]
      exact Finset.prod_ne_zero_iff.2 fun s hs => pow_ne_zero _ (hp0 s (Finset.mem_range.1 hs))
    have hxy : (x : C.V) = y' := by
      apply smul_cancel κ hκ0
      rw [hyy, ← hκE]
    rw [hxy]
    exact hy'

end Formalism.MainNotions.N.Ln03.Pf

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfSplit
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

theorem unitStep_holds {e : W.DD W.one} (hUnitGen : UnitGen W e) (hCrysOne : IsCrys PD W.one.ρ) :
    UnitStep W e := by
  have hB := unitBasis_of hUnitGen hCrysOne
  have hγ : ∀ g, W.γD W.one g e = e := hUnitGen.2.2.1
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨hc1, hc2⟩ := hc ()
    simp only [lc, Fintype.sum_unique]
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [← smul_assoc, hc1]
    · rw [W.γD_smul, hγ, hc2 δ hδ]
  · intro c c' _ _ h
    simp only [lc, Fintype.sum_unique] at h
    funext u
    obtain ⟨ε, _, huniq⟩ := hB (c () • e)
    exact (huniq (c u) rfl).trans (huniq (c' u) h).symm
  · intro x hx
    obtain ⟨ε, hε, huniq⟩ := hB x
    obtain ⟨h1, h2⟩ := hx
    refine ⟨fun _ => ε, fun _ => ⟨?_, fun δ hδ => ?_⟩, ?_⟩
    · have hx' : x = ((letE i : LetA O n) • ε) • e := by
        rw [smul_assoc, ← hε, h1]
      exact huniq _ hx'
    · have hx' : x = W.γE δ ε • e := by
        conv_lhs => rw [← h2 δ hδ, hε]
        rw [W.γD_smul, hγ]
      exact huniq _ hx'
    · simp only [lc, Fintype.sum_unique]
      exact hε.symm

theorem splitStep_holds (hOloc : IsLocalRing O)
    (hOnil : ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ (N : ℕ) (d : O), c ^ N = ((PD.p : ℕ) : O) * d)
    (hs : W.s = 1) (hp2 : PD.p ≠ 2) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W)
    (hJ : ∀ T : LocLat G Qp LL O, CrysLat PD T → ∃ M h : ZMod n → ℕ, Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h) :
    SplitStep W := by
  intro T₁ T₂ F hc₁ hc₂ hon
  obtain ⟨m₁, B₁, hB₁, -⟩ := exists_basis_Delta_fixed_mem_N hP9 hs hp2 T₁ hc₁.2.2.2
  obtain ⟨m₂, B₂, hB₂, hB₂N⟩ := exists_basis_Delta_fixed_mem_N hP9 hs hp2 T₂ hc₂.2.2.2
  have hcu := isUnit_card_finiteDelta hP9 hs hp2 T₁ hc₁.2.2.2
  have hlift : ∀ k, ∃ w : W.DD T₁, (∀ δ ∈ W.DelF, W.γD T₁ δ w = w) ∧ W.map F w = B₂ k := by
    intro k
    obtain ⟨w₀, hw₀⟩ := exists_lift_of_onto hs hLem3 hJ F hc₁ hc₂ hon (B₂ k) (hB₂N k)
    exact exists_invariant_lift_average hcu F w₀ (B₂ k) (hB₂ k) hw₀
  choose w hwΔ hwF using hlift
  refine ⟨m₂, m₁ - m₂, fun i => ?_⟩
  have hloc := letterRing_isLocalRing (W := W) hOloc hOnil i
  set M : Fin m₁ → Fin m₂ → W.EE := fun l k => B₂.repr (W.map F (B₁ l)) k with hMdef
  have hMγ : ∀ l k, ∀ δ ∈ W.DelF, W.γE δ (M l k) = M l k := by
    intro l k δ hδ
    rw [hMdef, ← basis_repr_gamma B₂ hB₂ _ δ hδ, ← W.map_γ, hB₁ l δ hδ]
  have hM : ∀ l k, k17e W i * M l k ∈ EEl W i := by
    intro l k
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [idempotent_smul_eq_mul, ← mul_assoc, idempotent_mul_self_bis]
    · rw [map_mul, idempotent_gamma_invariant, hMγ l k δ hδ]
  choose μ hμ using fun l k => letterRing_val_surjective i _ (hM l k)
  have hcoef : ∀ (u : Fin m₁ → k17R W i) (k : Fin m₂),
      letterRingVal W i (k17f μ u k) = ∑ l, letterRingVal W i (u l) * M l k := by
    intro u k
    change letterRingVal W i (∑ l, u l * μ l k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [letterRing_val_mul, hμ, ← mul_assoc, letterRing_mul_idempotent]
  have hmap : ∀ u : Fin m₁ → k17R W i, W.map F (∑ l, letterRingVal W i (u l) • B₁ l) =
      ∑ k, letterRingVal W i (k17f μ u k) • B₂ k := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hcoef, Finset.sum_smul, map_sum, map_smul]
    have h1 : ∀ l, W.map F (B₁ l) = ∑ k, M l k • B₂ k := fun l => (B₂.sum_repr _).symm
    simp only [h1, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  have hstd : ∀ k, ∃ u : Fin m₁ → k17R W i, k17f μ u = Pi.single k 1 := by
    intro k
    have hd : ∀ l, k17e W i * B₁.repr (w k) l ∈ EEl W i := by
      intro l
      refine ⟨?_, fun δ hδ => ?_⟩
      · rw [idempotent_smul_eq_mul, ← mul_assoc, idempotent_mul_self_bis]
      · rw [map_mul, idempotent_gamma_invariant, ← basis_repr_gamma B₁ hB₁ _ δ hδ, hwΔ k δ hδ]
    obtain ⟨u, hu⟩ := exists_preimage_letter_ring i _ hd
    refine ⟨u, funext fun k' => letterRing_val_injective i ?_⟩
    have h1 : ∑ l, letterRingVal W i (u l) • B₁ l = k17e W i • w k := by
      simp only [hu, ← smul_smul, ← Finset.smul_sum, B₁.sum_repr]
    have h2 := hmap u
    rw [h1, map_smul, hwF] at h2
    have h3 : k17e W i • B₂ k = ∑ k', letterRingVal W i ((Pi.single k 1 : Fin m₂ → k17R W i) k') • B₂ k' := by
      simp only [Pi.single_apply]
      simp only [apply_ite (letterRingVal W i), map_zero, letterRing_val_one, ite_smul, zero_smul]
      rw [Finset.sum_ite_eq']
      simp
    rw [h3] at h2
    exact congrFun (basis_coefficients_unique B₂ h2.symm) k'
  choose ν hν using hstd
  have hsurj : Function.Surjective (k17f μ) := by
    intro y
    refine ⟨∑ k, y k • ν k, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, hν]
    funext k'
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨C, hCl, hCr⟩ := exists_basis_of_surjective (k17f μ) hsurj
  refine ⟨fun t => ∑ l, letterRingVal W i (C t l) • B₁ l,
    fun j => ∑ l, letterRingVal W i (Pi.basisFun (k17R W i) (Fin m₂) j l) • B₂ l,
    letter_invariants_basis B₁ hB₁ i C, letter_invariants_basis B₂ hB₂ i (Pi.basisFun _ _), fun j => ?_, fun j => ?_⟩
  · rw [hmap, hCl]
    simp only [Pi.basisFun_apply]
  · rw [hmap, hCr]
    simp

end Formalism.MainNotions.N.Ln03.Pf
end
end

