module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSubgroupOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousCharacterCompactUnitValues
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

private theorem norm_le_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range hψ.norm).bddAbove
  by_contra hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hlt)
  have := hC ⟨s ^ n, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hn (not_lt.2 this)

private theorem norm_eq_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ = 1 := by
  refine le_antisymm (norm_le_one ψ hψ s) ?_
  have h := norm_le_one ψ hψ s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h
  exact (inv_le_one₀ (norm_pos_iff.2 (ψ s).ne_zero)).1 h

theorem UpperTheory.continuous_character_compact_unit_values :
    UpperTheory.V.Af.Wd.CharEnd := by
  intro F Ω _ _ _ _ _ l hl ι w A h hw ψ a hψ hσ
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have hq1 : 1 < normV w := GlobalTheory.WeilDeligne.one_lt_normV w
  have hpow := normV_eq_pow (l := l) hw
  have hf : resDeg l w ≠ 0 := by
    intro h0
    rw [hpow, h0, pow_zero] at hq1
    exact lt_irrefl _ hq1
  have hl1 : ‖(l : Qbar l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hlt : ‖((normV w : ℕ) : Qbar l)‖ < 1 := by
    rw [hpow, Nat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hl1 hf
  have hpos : 0 < ‖((normV w : ℕ) : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (by omega))
  have ha : a = 0 := by
    have h1 := hσ (frob h)
    rw [deg_frob, mul_one, ← map_natCast ι, ← map_zpow₀] at h1
    have h2 := norm_eq_one ψ hψ (Subgroup.inclusion (Weil_le_Dec h) (frob h))
    rw [ι.injective h1, norm_zpow] at h2
    exact (zpow_eq_one_iff_right₀ hpos.le hlt.ne).1 h2
  refine ⟨ha, ?_⟩
  have hd := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  have he : (fun s => (ψ s : Qbar l)) = fun _ => 1 := by
    refine hd.equalizer hψ continuous_const (funext fun σ => ?_)
    have h1 := hσ σ
    rw [ha, zero_mul, zpow_zero, ← map_one ι] at h1
    exact ι.injective h1
  ext s
  simpa using congrFun he s
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallineFrobeniusAlgebraicElements
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial
open GlobalTheory.UnramifiedCrys

private def algSub (p : ℕ) [hp : Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_pos hp.out.pos _).ne'⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  neg_mem' := by
    rintro x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    have h := sub_pow_char_pow (p := p) (n := a) (0 : R) x
    rwa [zero_sub, hx, zero_pow (pow_pos hp.out.pos _).ne', zero_sub] at h

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ g (f : R →+* R), (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → f y = ρ g y) →
        (M g).map (zlW p R) * W.map (WittVector.map f) = W :=
  _root_.UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg ρ hopen M hM hJ

private theorem map_iterFrob {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (k : ℕ)
    (x : WittVector p R) :
    WittVector.map (iterateFrobenius R p (k + 1)) x =
      WittVector.frobenius (WittVector.map (iterateFrobenius R p k) x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext i
  simp [iterateFrobenius_def, frobenius_def, pow_succ, pow_mul]

private theorem φB_pow_ιA {l : ℕ} [Fact l.Prime] (k : ℕ) (x : WittVector l (OCb l)) :
    ((PP l).φB ^ k) ((AIP l).ιA x) = (AIP l).ιA (WittVector.map (iterateFrobenius _ l k) x) := by
  induction k with
  | zero =>
    rw [pow_zero]
    change (AIP l).ιA x = _
    congr 1
    ext i
    simp
  | succ k ih =>
    rw [pow_succ', map_iterFrob, (AIP l).ιA_φ, ← ih]
    rfl

open GlobalTheory.UnramifiedRep GlobalTheory.Cyc in
theorem UpperTheory.crystalline_frobenius_algebraic_elements :
    UpperTheory.V.Af.Wd.WittPer := by
  intro l _ K r M hM hMI
  obtain ⟨-, -, hI, -, -⟩ := iqBasic l
  obtain ⟨Ti⟩ := tiedP l
  have := compactSpace_GK K
  obtain ⟨W, hW, hWg⟩ := exists_alg (p := l) ((AIP l).actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq (AIP l) y m hm hy)) M hM
    (fun g hg => hMI g ((hI g).2 (norm_sub_lt_one_of_fix (AIP l) g hg)))
  have key : ∀ (g : ↥(GK K)) (f : OCb l →+* OCb l) (F : Bcr l → Bcr l),
      (∀ m, 0 < m → ∀ y : OCb l, y ^ l ^ m = y → f y = (AIP l).actT g y) →
      (∀ x, F ((AIP l).ιA x) = (AIP l).ιA (WittVector.map f x)) →
      (M g).map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l])) * ((AIP l).ιA.mapMatrix W).map F =
        (AIP l).ιA.mapMatrix W := fun g f F hf hF => by
    conv_rhs => rw [← hWg g f hf, map_mul]
    congr 1
    · ext i j
      exact (ιA_zlW (AIP l) Ti (M g i j)).symm
    · ext i j
      exact hF _
  refine ⟨(AIP l).ιA.mapMatrix W, ?_, fun g => ?_, fun g k hk => ?_⟩
  · rw [← RingHom.map_det]
    exact hW.map _
  · exact key g ((AIP l).actT g).toRingHom _ (fun _ _ _ _ => rfl) fun x => ((AIP l).ιA_act g x).symm
  · exact key g (iterateFrobenius _ l k) _
      (fun m hm y hy => (UpperTheory.tilt_frobenius_teichmuller_action l y m hm hy g k hk).symm) fun x => φB_pow_ιA k x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DpstRightExact
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

private theorem count_dims {F D' D D'' : Type} [Field F] [AddCommGroup D'] [Module F D'] [AddCommGroup D] [Module F D]
    [AddCommGroup D''] [Module F D''] (j : D' →ₗ[F] D) (q : D →ₗ[F] D'') (hj : Function.Injective j)
    (hex : Function.Exact j q) (a c : ℕ) (h' : Module.rank F D' ≤ a) (h'' : Module.rank F D'' ≤ c)
    (h : Module.rank F D = (a + c : ℕ)) :
    Module.rank F D' = a ∧ Module.rank F D'' = c ∧ Function.Surjective q := by
  haveI : FiniteDimensional F D' := Module.rank_lt_aleph0_iff.mp (h'.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI : FiniteDimensional F D'' := Module.rank_lt_aleph0_iff.mp (h''.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI : FiniteDimensional F D := Module.rank_lt_aleph0_iff.mp (h.le.trans_lt (Cardinal.natCast_lt_aleph0))
  rw [← finrank_eq_rank] at h' h'' h
  rw [← finrank_eq_rank, ← finrank_eq_rank]
  have e1 : finrank F D' ≤ a := Nat.cast_le.mp h'
  have e2 : finrank F D'' ≤ c := Nat.cast_le.mp h''
  have e3 : finrank F D = a + c := Nat.cast_injective h
  have e4 := q.finrank_range_add_finrank_ker
  have e5 : finrank F (LinearMap.ker q) = finrank F D' := by
    rw [LinearMap.exact_iff.mp hex, LinearMap.finrank_range_of_inj hj]
  have e6 : finrank F (LinearMap.range q) ≤ finrank F D'' := Submodule.finrank_le _
  refine ⟨by rw [show finrank F D' = a by omega], by rw [show finrank F D'' = c by omega], ?_⟩
  rw [← LinearMap.range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (by omega)

private noncomputable def dmapUr {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'}
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) : DpstUr P ρ →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ' where
  toFun := fun x => toUr P ρ' (dmap P hf ((toUr P ρ).symm x))
  map_add' := fun x y => by simp only [map_add (f := _)]
  map_smul' := fun c x => dmap_mulD P hf c ((toUr P ρ).symm x)

theorem UpperTheory.dpst_right_exact :
    UpperTheory.V.Af.Wd.DRight := by
  intro l _ K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l (UpperTheory.V.Loc.PP l) (UpperTheory.V.Loc.AIP l) (UpperTheory.V.Loc.tiedP l)
  haveI : FiniteDimensional ℚ_[l] ↥L.1 := L.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥L.1 V
  haveI : FiniteDimensional ℚ_[l] V' := Module.Finite.of_injective (f.restrictScalars ℚ_[l]) hfi
  haveI : FiniteDimensional ℚ_[l] V'' := Module.Finite.of_surjective (p.restrictScalars ℚ_[l]) hps
  obtain ⟨hdi, hdex⟩ := UpperTheory.weilDeligne_dpst_leftExact l (UpperTheory.V.Loc.PP l) K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hex
  have h' := _root_.GlobalTheory.PstRank.rank_DpstUr_le (UpperTheory.V.Loc.PP l) hdom hreg ρ'
  have h'' := _root_.GlobalTheory.PstRank.rank_DpstUr_le (UpperTheory.V.Loc.PP l) hdom hreg ρ''
  have hsum : finrank ℚ_[l] V = finrank ℚ_[l] V' + finrank ℚ_[l] V'' := by
    have hexq : Function.Exact (f.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := hex
    have e4 := (p.restrictScalars ℚ_[l]).finrank_range_add_finrank_ker
    rw [LinearMap.exact_iff.mp hexq, LinearMap.finrank_range_of_inj (f := f.restrictScalars ℚ_[l]) hfi,
      LinearMap.range_eq_top.mpr (show Function.Surjective (p.restrictScalars ℚ_[l]) from hps), finrank_top] at e4
    omega
  have h : Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr (UpperTheory.V.Loc.PP l) ρ) = (finrank ℚ_[l] V' + finrank ℚ_[l] V'' : ℕ) := by
    rw [← hsum, finrank_eq_rank]; exact hV
  obtain ⟨r1, r2, r3⟩ := count_dims (dmapUr (UpperTheory.V.Loc.PP l) hf) (dmapUr (UpperTheory.V.Loc.PP l) hp) hdi hdex _ _ h' h'' h
  rw [finrank_eq_rank] at r1 r2
  exact ⟨r1, r2, r3⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsTypeWeilDeligneIffMonodromyZeroCharpoly
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open Formalism.MainNotions.N (IsSSRep IsInv)
open scoped Matrix

private noncomputable def diagRep {G : Type} [Group G] {n : ℕ} (χ : Fin n → G →* ℂˣ) : G →* GL (Fin n) ℂ :=
  (Units.map (Matrix.diagonalRingHom (Fin n) ℂ).toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun _ : Fin n => ℂ)).symm.toMonoidHom.comp (MonoidHom.pi χ))

private theorem commute_of_semisimple_of_charpoly_prod_chars {G : Type} [Group G] {m n : ℕ} (T : G →* Module.End ℂ (Fin m → ℂ))
    (χ : Fin n → G →* ℂˣ) (hss : ∀ g, (T g).IsSemisimple)
    (hcp : ∀ g, (T g).charpoly = ∏ i, (X - C ((χ i g : ℂˣ) : ℂ))) (g k : G) :
    Commute (T g) (T k) := by
  have hone : T (g * k * g⁻¹ * k⁻¹) = 1 := by
    have h1 : (T (g * k * g⁻¹ * k⁻¹)).charpoly = (X - C (1 : ℂ)) ^ n := by
      rw [hcp]
      have : ∀ i, ((χ i (g * k * g⁻¹ * k⁻¹) : ℂˣ) : ℂ) = 1 := by
        intro i
        simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
      simp [this]
    have hdvd : minpoly ℂ (T (g * k * g⁻¹ * k⁻¹)) ∣ (X - C (1 : ℂ)) ^ n :=
      h1 ▸ LinearMap.minpoly_dvd_charpoly _
    have hd : minpoly ℂ (T (g * k * g⁻¹ * k⁻¹)) ∣ X - C (1 : ℂ) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact dvd_trans (by simpa using hdvd) (one_dvd _)
      · exact ((hss _).minpoly_squarefree.dvd_pow_iff_dvd hn.ne').mp hdvd
    have := (minpoly.dvd_iff).mp hd
    simpa [sub_eq_zero] using this
  have hgk : g * k = (g * k * g⁻¹ * k⁻¹) * (k * g) := by group
  have h2 : T (g * k) = T (g * k * g⁻¹ * k⁻¹) * T (k * g) := by
    rw [← map_mul, ← hgk]
  rw [hone, one_mul, map_mul, map_mul] at h2
  exact h2

private theorem exists_basis_eigen_of_semisimple_commuting {G : Type} [Group G] {m : ℕ} (T : G →* Module.End ℂ (Fin m → ℂ))
    (hss : ∀ g, (T g).IsSemisimple) (hc : ∀ g k, Commute (T g) (T k)) :
    ∃ (b : Module.Basis (Fin m) ℂ (Fin m → ℂ)) (c : Fin m → G → ℂ), ∀ j g, T g (b j) = c j g • b j := by
  classical
  let A : (G → ℂ) → Submodule ℂ (Fin m → ℂ) := fun φ => ⨅ g, (T g).maxGenEigenspace (φ g)
  have hmaps : ∀ (g k : G) (μ : ℂ), Set.MapsTo (T g) ((T k).maxGenEigenspace μ) ((T k).maxGenEigenspace μ) :=
    fun g k μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc k g) μ
  have hind : iSupIndep A :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun g => T g) hmaps
  have htop : iSup A = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun g => T g) hmaps
      (fun g => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hint : DirectSum.IsInternal A := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let v : (φ : G → ℂ) → Module.Basis (Module.Free.ChooseBasisIndex ℂ (A φ)) ℂ (A φ) :=
    fun φ => Module.Free.chooseBasis ℂ (A φ)
  let b0 := hint.collectedBasis v
  let e := b0.indexEquiv (Pi.basisFun ℂ (Fin m))
  refine ⟨b0.reindex e, fun j => (e.symm j).1, fun j g => ?_⟩
  have hmem : b0 (e.symm j) ∈ A (e.symm j).1 := hint.collectedBasis_mem v _
  have hmem' : b0 (e.symm j) ∈ (T g).eigenspace ((e.symm j).1 g) := by
    have := (Submodule.mem_iInf _).mp hmem g
    rwa [(hss g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at this
  rw [Module.Basis.reindex_apply]
  exact Module.End.mem_eigenspace_iff.mp hmem'

private theorem exists_linearEquiv_diagonal_chars_of_eigenbasis {G : Type} [Group G] {m n : ℕ} (T : G →* Module.End ℂ (Fin m → ℂ)) (χ : Fin n → G →* ℂˣ)
    (hcp : ∀ g, (T g).charpoly = ∏ i, (X - C ((χ i g : ℂˣ) : ℂ)))
    (b : Module.Basis (Fin m) ℂ (Fin m → ℂ)) (c : Fin m → G → ℂ) (hT : ∀ j g, T g (b j) = c j g • b j) :
    ∃ e : (Fin m → ℂ) ≃ₗ[ℂ] (Fin n → ℂ),
      ∀ g v, e (T g v) = Matrix.toLin' (Matrix.diagonal fun i => ((χ i g : ℂˣ) : ℂ)) (e v) := by
  classical
  have hinj : ∀ j, Function.Injective fun z : ℂ => z • b j := fun j => smul_left_injective ℂ (b.ne_zero j)
  have hone : ∀ j, c j 1 = 1 := by
    intro j
    apply hinj j
    simp only
    rw [← hT, map_one, one_smul]
    rfl
  have hmul : ∀ j g k, c j (g * k) = c j g * c j k := by
    intro j g k
    apply hinj j
    simp only
    rw [← hT, map_mul, Module.End.mul_apply, hT, map_smul, hT, smul_smul, mul_comm]
  let ψ : Fin m → (G →* ℂ) := fun j => ⟨⟨c j, hone j⟩, hmul j⟩
  let χ' : Fin n → (G →* ℂ) := fun i => (Units.coeHom ℂ).comp (χ i)
  have hroots : ∀ {k : ℕ} (d : Fin k → ℂ), (∏ j, (X - C (d j))).roots = Finset.univ.val.map d := by
    intro k d
    rw [Finset.prod_eq_multiset_prod,
      show Finset.univ.val.map (fun j => X - C (d j)) = (Finset.univ.val.map d).map (fun a => X - C a) by
        rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C]
  have hdiag : ∀ g, LinearMap.toMatrix b b (T g) = Matrix.diagonal fun j => c j g := by
    intro g
    ext i j
    rw [LinearMap.toMatrix_apply, hT, map_smul, b.repr_self, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h, h]
  have hsum : ∀ g, ∑ j, c j g = ∑ i, ((χ i g : ℂˣ) : ℂ) := by
    intro g
    have hp := LinearMap.charpoly_toMatrix (T g) b
    rw [hdiag, Matrix.charpoly_diagonal, hcp] at hp
    have := congrArg (fun p => p.roots.sum) hp
    simpa [hroots, Finset.sum_eq_multiset_sum] using this
  have hcount : ∀ φ : G →* ℂ,
      Fintype.card {j // ψ j = φ} = Fintype.card {i // χ' i = φ} := by
    intro φ
    have hli := linearIndependent_monoidHom G ℂ
    set l : (G →* ℂ) →₀ ℂ := ∑ j, Finsupp.single (ψ j) 1 - ∑ i, Finsupp.single (χ' i) 1 with hl
    have hlc : Finsupp.linearCombination ℂ (fun f : G →* ℂ => (f : G → ℂ)) l = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hl, map_sub, map_sum, map_sum]
      simp only [Finsupp.linearCombination_single, one_smul]
      funext g
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.zero_apply]
      have := hsum g
      simp only [ψ, χ', MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.coe_comp, Function.comp_apply,
        Units.coeHom_apply]
      rw [this, sub_self]
    have hl0 : l = 0 := linearIndependent_iff.mp hli l hlc
    have hφ := congrArg (fun f => f φ) hl0
    simp only [hl, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.single_apply,
      Finsupp.coe_zero, Pi.zero_apply, Finset.sum_boole, sub_eq_zero] at hφ
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact_mod_cast hφ
  let π : Fin m ≃ Fin n := Equiv.ofFiberEquiv (f := ψ) (g := χ') fun φ => Fintype.equivOfCardEq (hcount φ)
  have hπ : ∀ j, χ' (π j) = ψ j := fun j => Equiv.ofFiberEquiv_map _ j
  have hcoord : ∀ g v k, b.repr (T g v) k = c k g * b.repr v k := by
    intro g v k
    have := b.ext (f₁ := (Finsupp.lapply k).comp (b.repr.toLinearMap.comp (T g)))
      (f₂ := c k g • (Finsupp.lapply k).comp b.repr.toLinearMap) (by
        intro j
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hT, map_smul, b.repr_self,
          Finsupp.lapply_apply, LinearMap.smul_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        by_cases h : j = k
        · subst h; simp
        · simp [h])
    simpa using LinearMap.congr_fun this v
  refine ⟨b.equivFun.trans (LinearEquiv.funCongrLeft ℂ ℂ π.symm), fun g v => ?_⟩
  ext i
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Module.Basis.equivFun_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal, hcoord]
  congr 1
  have h1 := hπ (π.symm i)
  rw [Equiv.apply_symm_apply] at h1
  have h2 := congrArg (fun f : G →* ℂ => f g) h1
  simpa [ψ, χ'] using h2.symm

theorem UpperTheory.isTypeWeilDeligne_iff_monodromy_zero_charpoly :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (χ : Fin n → Ine (F := L) A →* ℂˣ) (x : WD h), IsTypeWD h χ x ↔ x.mono0 ∧ ∀ s, x.charPol (ineIncl h s) = ∏ i, (X - C (χ i s : ℂ)) := by
  intro L Ω _ _ _ _ _ n w A h χ x
  constructor
  · rintro ⟨b, rfl, hN, hb⟩
    refine ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff b).mpr hN, fun s => ?_⟩
    rw [WD.charPol_mk, hb, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]
  · rintro ⟨h0, hc⟩
    obtain ⟨m, a, rfl⟩ := WD.exists_rep x
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
    let T : ↥(Ine (F := L) A) →* Module.End ℂ (Fin m → ℂ) := a.ρ.comp (ineIncl h)
    have hss : ∀ g, (T g).IsSemisimple := fun g => a.semisimple _
    have hcp : ∀ g, (T g).charpoly = ∏ i, (X - C ((χ i g : ℂˣ) : ℂ)) := by
      intro g
      have := hc g
      rwa [WD.charPol_mk] at this
    obtain ⟨bs, c, hT⟩ := exists_basis_eigen_of_semisimple_commuting T hss (commute_of_semisimple_of_charpoly_prod_chars T χ hss hcp)
    obtain ⟨e, he⟩ := exists_linearEquiv_diagonal_chars_of_eigenbasis T χ hcp bs c hT
    refine ⟨a.transport e, ?_, ?_, ?_⟩
    · refine (WD.sound ⟨e, fun σ v => ?_, fun v => ?_⟩).symm
      · simp [WDRep.transport]
      · simp [WDRep.transport]
    · simp [WDRep.transport, h0]
    · intro s
      apply LinearMap.ext
      intro u
      have := he s (e.symm u)
      simp only [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      simp [WDRep.transport, T]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsotypicSeparatesAndEmbedsIntoInvariantSubspace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne UpperTheory.V.Hi
open UpperTheory.V.W (Plc)

private theorem sepMod {R M S ι : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (Φ : (ι →₀ S) →ₗ[R] M) (hs : Function.Surjective Φ) (x : M) (hx : x ≠ 0) :
    ∃ p : M →ₗ[R] S, p x ≠ 0 := by
  obtain ⟨s, hs'⟩ := IsSemisimpleModule.lifting_property Φ hs (LinearMap.id : M →ₗ[R] M)
  have h0 : s x ≠ 0 := fun e => hx (by rw [← LinearMap.id_apply (R := R) x, ← hs', LinearMap.comp_apply, e, map_zero])
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h0
  exact ⟨Finsupp.lapply i ∘ₗ s, hi⟩

private theorem sepRep {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (hρ : ρ'.IsIrreducible)
    (h : ∀ y, y ∈ ⨆ f : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)}, LinearMap.range f.1) (x : V) (hx : x ≠ 0) :
    ∃ p : V →ₗ[ℂ] V', (∀ g v, p (ρ g v) = ρ' g (p v)) ∧ p x ≠ 0 := by
  classical
  let F : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)} → ρ'.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρ' ρ ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
  let Φ := Finsupp.lsum ℕ F
  have hs : Function.Surjective Φ := fun y => by
    refine Submodule.iSup_induction _ (motive := fun y : V => ∃ z, Φ z = y) (h y) ?_ ⟨0, map_zero Φ⟩ ?_
    · rintro f _ ⟨v, rfl⟩
      exact ⟨Finsupp.single f v, Finsupp.lsum_single _ _ _ _⟩
    · rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
      exact ⟨z + z', map_add Φ z z'⟩
  obtain ⟨p, hp⟩ := sepMod Φ hs x hx
  let q := (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ').symm p
  exact ⟨q.toLinearMap, fun g v => q.isIntertwining _ _ g v, hp⟩

private def piRep {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (ι : Type) :
    Representation ℂ G (ι → M) where
  toFun g := (ρ g).compLeft ι
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

private theorem piIso {G M S : Type} [Group G] [AddCommGroup M] [Module ℂ M] [AddCommGroup S] [Module ℂ S]
    (ρ : Representation ℂ G M) (σ : Representation ℂ G S) (ι : Type) [Finite ι]
    (h : ∀ y, y ∈ ⨆ f : {f : S →ₗ[ℂ] M // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) (y : ι → M) :
    y ∈ ⨆ f : {f : S →ₗ[ℂ] (ι → M) // ∀ g v, f (σ g v) = piRep ρ ι g (f v)}, LinearMap.range f.1 := by
  classical
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine Submodule.iSup_induction _ (motive := fun z : M => (Pi.single i z : ι → M) ∈ _) (h (y i)) ?_ ?_ ?_
  · rintro f _ ⟨v, rfl⟩
    refine Submodule.mem_iSup_of_mem ⟨LinearMap.single ℂ (fun _ : ι => M) i ∘ₗ f.1, fun g v => ?_⟩ ⟨v, rfl⟩
    funext j
    change (Pi.single i (f.1 (σ g v)) : ι → M) j = ρ g ((Pi.single i (f.1 v) : ι → M) j)
    by_cases hj : j = i
    · subst hj; simp [f.2]
    · simp [Pi.single_eq_of_ne hj]
  · simp
  · intro a b ha hb
    rw [Pi.single_add]; exact add_mem ha hb

theorem UpperTheory.isotypic_separates_and_embeds_into_invariant_subspace :
    ∀ (H M : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) (σ : SmIrr H), IsoSum ρ ⊤ σ → (∀ x : M, x ≠ 0 → ∃ p : M →ₗ[ℂ] σ.V, (∀ g v, p (ρ g v) = σ.ρ g (p v)) ∧ p x ≠ 0) ∧ ∀ (ι : Type) [Finite ι] (Y : Submodule ℂ (ι → M)), Y ≠ ⊥ → (∀ g, ∀ F ∈ Y, (fun i => ρ g (F i)) ∈ Y) → ∃ s : σ.V →ₗ[ℂ] (ι → M), Function.Injective s ∧ (∀ v, s v ∈ Y) ∧ ∀ g v i, s (σ.ρ g v) i = ρ g (s v i) := by
  intro H M _ _ _ _ _ ρ σ hI
  have h : ∀ y, y ∈ ⨆ f : {f : σ.V →ₗ[ℂ] M // ∀ g v, f (σ.ρ g v) = ρ g (f v)}, LinearMap.range f.1 := fun y => by
    refine (le_trans hI (iSup_le fun f => ?_)) (Submodule.mem_top (x := y))
    exact le_iSup_of_le (f := fun f : {f : σ.V →ₗ[ℂ] M // ∀ g v, f (σ.ρ g v) = ρ g (f v)} => LinearMap.range f.1)
      ⟨f.1, f.2.1⟩ le_rfl
  refine ⟨sepRep ρ σ.ρ σ.irred h, fun ι _ Y hY hst => ?_⟩
  let π : Representation ℂ H Y := (piRep ρ ι).subrepresentation Y fun g F hF => hst g F hF
  have h2 := UpperTheory.V.PiLin.iso_sub σ.ρ π (piRep ρ ι) σ.irred Y.subtype Y.injective_subtype (fun _ _ => rfl)
    fun y => piIso ρ σ.ρ ι h _
  obtain ⟨f, hf⟩ : ∃ f : {f : σ.V →ₗ[ℂ] Y // ∀ g v, f (σ.ρ g v) = π g (f v)}, f.1 ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff Y).1 hY
    have := h2 ⟨y, hy⟩
    simp only [hc, LinearMap.range_zero, iSup_bot, Submodule.mem_bot] at this
    exact hy0 (congrArg Subtype.val this)
  haveI := σ.irred
  have hi : Function.Injective f.1 := by
    let F : σ.ρ.IntertwiningMap π := ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
    rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
    · exact hi
    · exact absurd (congrArg Representation.IntertwiningMap.toLinearMap hz) hf
  refine ⟨Y.subtype ∘ₗ f.1, Y.injective_subtype.comp hi, fun v => (f.1 v).2, fun g v i => ?_⟩
  exact congrFun (congrArg Subtype.val (f.2 g v)) i
end

