module

public import Mathlib
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0038
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LevelRepOneLe
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

theorem finite_card_dual {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V] :
    Finite (Module.Dual F V) ∧ Nat.card (Module.Dual F V) = Nat.card V := by
  haveI : Module.Finite F V := Module.Finite.of_finite
  haveI : Finite (Module.Dual F V) := DFunLike.finite (Module.Dual F V)
  refine ⟨inferInstance, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := F), Module.natCard_eq_pow_finrank (K := F) (V := V),
    Subspace.dual_finrank_eq]

theorem card_H2_level_rep_le :
    Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M)
    (h : ((p : O) ^ 1) ∈ Ideal.span {ϖ ^ 1}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ) →
    Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ)) ≤ Nat.card (IsLocalRing.ResidueField O) := by
  intro hT p _ K hK O _ _ _ _ ϖ hϖ M _ _ e ρ h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
  intro hc
  obtain ⟨hfin, hcard⟩ := _root_.GlobalTheory.ShapeNeg.levKO_card hϖ e 1
  haveI : Finite (Lev M (ϖ ^ 1)) := hfin
  haveI : Fact (p ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  obtain ⟨⟨eH⟩, -, -, -, hb⟩ := hT p K hK 1 (Lev M (ϖ ^ 1)) (levRepZ p 1 h ρ) one_pos hc
  set ρ' := levRepZ p 1 h ρ
  set χ := Formalism.GaloisCohomology.cycK p K 1

  let W := ↥(H0 ((twDual χ ρ').comp (MonoidHom.id _)))
  haveI : Finite (TDual (ZMod (p ^ 1)) (Lev M (ϖ ^ 1))) :=
    (finite_card_dual (F := ZMod (p ^ 1)) (V := Lev M (ϖ ^ 1))).1
  haveI : Finite W := Subtype.finite
  have hW : Nat.card W ≤ Nat.card (Lev M (ϖ ^ 1)) :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (finite_card_dual (F := ZMod (p ^ 1)) (V := Lev M (ϖ ^ 1))).2.le
  obtain ⟨hfd, hcd⟩ := finite_card_dual (F := ZMod (p ^ 1)) (V := W)
  let E := LinearEquiv.congrRight (M := W) eH
  haveI : Finite (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) :=
    Finite.of_equiv _ E.symm.toEquiv
  have h1 : Nat.card (H2 ρ') ≤ Nat.card (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) :=
    Nat.card_le_card_of_injective _ hb.1
  have h2 : Nat.card (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) = Nat.card W :=
    (Nat.card_congr E.toEquiv).trans hcd
  calc Nat.card (H2 ρ') ≤ Nat.card W := h1.trans h2.le
    _ ≤ Nat.card (Lev M (ϖ ^ 1)) := hW
    _ = Nat.card (IsLocalRing.ResidueField O) := hcard.trans (pow_one _)

end GlobalTheory.ShapeNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOntoOfUnramified
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.UnramCyc


open PowerSeries in
theorem _root_.GlobalTheory.UnramCyc.chi_onto_of_unramified : ∀ {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (K : _root_.Formalism.BasicNotions.Loc.FinExt l),
    K.1 ≤ _root_.Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l → ∀ c : ℤ_[l]ˣ, ∃ g ∈ _root_.Formalism.BasicNotions.Loc.GK K, (P.χQ g : ℚ_[l]) = ((c : ℤ_[l]) : ℚ_[l]) := by
  intro l _ P K hK c
  have hnorm : ‖((c : ℤ_[l]) : ℚ_[l])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_units c
  obtain ⟨g, hg, hgc⟩ := _root_.GlobalTheory.Cyc.exists_chi_eq K P.χQ P.χQ_cyc _ hnorm
  have hK0 : _root_.Formalism.BasicNotions.Loc.K0 K = K.1 := by
    unfold _root_.Formalism.BasicNotions.Loc.K0
    exact inf_eq_left.mpr hK
  refine ⟨g, ?_, hgc⟩
  unfold _root_.Formalism.BasicNotions.Loc.GK
  rw [← hK0]
  exact hg

end GlobalTheory.UnramCyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContActionTorsionLevelZModOfIsLocallyConstantStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant : ∀ {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    (∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) →
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  first | exact @GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | exact GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | (intros; apply GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterIsLocallyConstantModPowStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_character_isLocallyConstant_mod_pow : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O]
    (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ N : ℕ,
    IsLocallyConstant (fun σ : Formalism.GaloisCohomology.GK p K => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O)) := by
  first | exact @GlobalTheory.ShapeNeg.cyclotomic_isLocallyConstant_mod | exact GlobalTheory.ShapeNeg.cyclotomic_isLocallyConstant_mod | (intros; apply GlobalTheory.ShapeNeg.cyclotomic_isLocallyConstant_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFree
section
open Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory

theorem dualLat_finite_free {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V V' : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V']
    [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) :
    IsLatticeIn T → PerfectRight b →
      Module.Finite O (dualLat b T) ∧ Module.Free O (dualLat b T) := by
  classical
  rintro ⟨⟨s, hs⟩, hspan⟩ hb
  have hsT : ∀ x ∈ s, x ∈ T := fun x hx => hs ▸ Submodule.subset_span hx
  have hmem : ∀ (f : dualLat b T) (x : s), ∃ o : O, algebraMap O (FractionRing O) o = b x f :=
    fun f x => Submodule.mem_one.mp (f.2 x (hsT x x.2))
  let g0 : dualLat b T → s → O := fun f x => Classical.choose (hmem f x)
  have hg0 : ∀ f x, algebraMap O (FractionRing O) (g0 f x) = b x f :=
    fun f x => Classical.choose_spec (hmem f x)
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  let g : dualLat b T →ₗ[O] (s → O) :=
    { toFun := g0
      map_add' := fun f f' => by
        funext x; apply hinj
        rw [Pi.add_apply, map_add (f := _), hg0, hg0, hg0, Submodule.coe_add, map_add (f := _)]
      map_smul' := fun c f => by
        funext x; apply hinj
        rw [Pi.smul_apply, smul_eq_mul, map_mul, hg0, hg0, Submodule.coe_smul, map_smul,
          RingHom.id_apply, Algebra.smul_def] }
  have ginj : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    have h0 : ∀ x ∈ s, b x f = 0 := fun x hx => by
      rw [← hg0 f ⟨x, hx⟩]
      have : g0 f ⟨x, hx⟩ = 0 := congrFun hf ⟨x, hx⟩
      rw [this, map_zero]
    have hT0 : T ≤ LinearMap.ker (b.flip (f : V')) := by
      intro x hx
      rw [← hs] at hx
      refine (Submodule.span_le.mpr ?_ : Submodule.span O (s : Set V) ≤ _) hx
      intro y hy
      simpa using h0 y hy
    let ψ : V →ₗ[FractionRing O] FractionRing O :=
      (b.flip (f : V')).extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)
    have hψ : ψ = 0 := by
      have : Submodule.span (FractionRing O) (T : Set V) ≤ LinearMap.ker ψ := by
        rw [Submodule.span_le]
        intro x hx
        have := hT0 hx
        simpa [ψ] using this
      rw [hspan, top_le_iff, LinearMap.ker_eq_top] at this
      exact this
    obtain ⟨f0, _, huniq⟩ := hb 0
    have e1 : (f : V') = f0 := huniq _ (fun x => by
      have := congrArg (fun φ => φ x) hψ
      simpa [ψ] using this)
    have e2 : (0 : V') = f0 := huniq _ (fun x => by simp)
    exact Subtype.ext (e1.trans e2.symm)
  have hfin : Module.Finite O (dualLat b T) := Module.Finite.of_injective g ginj
  have htf : Module.IsTorsionFree O (dualLat b T) :=
    Function.Injective.moduleIsTorsionFree g ginj (fun c m => g.map_smul c m)
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetInvAlgBaseChangeUnramifiedOdd
section
noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

namespace GlobalTheory.UnitLemma.Unr

theorem val_mul_of_ne {K : UQ} {a b : K.E} (ha : a ≠ 0) (hb : b ≠ 0) :
    val K.O (a * b) = val K.O a + val K.O b := by
  unfold val
  have ha' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a ≠ 0 := by simpa using ha
  have hb' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b ≠ 0 := by simpa using hb
  rw [map_mul, WithZero.log_mul ha' hb']; ring

theorem val_pow_of_ne {K : UQ} {a : K.E} (ha : a ≠ 0) (n : ℕ) : val K.O (a ^ n) = n * val K.O a := by
  induction n with
  | zero => simp [val]
  | succ n ih => rw [pow_succ, val_mul_of_ne (pow_ne_zero _ ha) ha, ih]; push_cast; ring

theorem eta_overExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (x : B.Aˣ), B.σ (x : B.A) = x → K'.eta ((overExt φ B ψ hψ hσ).gramDet (x : B.A)) = K.eta (B.gramDet (x : B.A)) := by
  intro K K' d φ hU hd B ψ hψ hσ x _
  have hd0 : 0 < d := hd.pos
  obtain ⟨w, hw0, hwv⟩ := GlobalTheory.T.exists_basis_trace_involution_det_unit_unramified K K' d φ hU hd0
  letI : Algebra K.E K'.E := φ.toAlgebra
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact hd0)
  letI : Algebra K'.E B.A := ψ.toAlgebra
  haveI : IsScalarTower K.E K'.E B.A := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  haveI : Module.Finite K'.E B.A := (overExt φ B ψ hψ hσ).fd
  set u := Module.finBasis K'.E B.A with hu
  set H : Matrix (Fin (Module.finrank K'.E B.A)) (Fin (Module.finrank K'.E B.A)) K'.E :=
    Matrix.of fun i j => Algebra.trace K'.E B.A ((x : B.A) * u i * B.σ (u j)) with hH
  have h1 : (overExt φ B ψ hψ hσ).gramDet (x : B.A) = H.det := rfl
  set b0 := w.smulTower u with hb0
  set e := b0.indexEquiv (Module.finBasis K.E B.A) with he
  rw [h1, ← Orbit.eta_gram B _ (b0.reindex e)]
  have h2 : (Matrix.of fun i j => B.herm x ((b0.reindex e) i) ((b0.reindex e) j)) =
      (Matrix.of fun (p q : Fin d × Fin (Module.finrank K'.E B.A)) =>
        Algebra.trace K.E K'.E (w p.1 * H p.2 q.2 * K'.c (w q.1))).submatrix e.symm e.symm := by
    ext i j
    simp only [Module.Basis.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, hb0,
      Module.Basis.smulTower_apply, InvAlg.herm, hH]
    rw [← Algebra.trace_trace (S := K'.E)]
    refine congrArg (Algebra.trace K.E K'.E) ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul B.σ]
    have hc : ∀ y : K'.E, B.σ (algebraMap K'.E B.A y) = algebraMap K'.E B.A (K'.c y) := hσ
    rw [hc]
    have : (x : B.A) * (algebraMap K'.E B.A (w (e.symm i).1) * u (e.symm i).2) *
        (algebraMap K'.E B.A (K'.c (w (e.symm j).1)) * B.σ (u (e.symm j).2)) =
        (w (e.symm i).1 * K'.c (w (e.symm j).1)) • ((x : B.A) * u (e.symm i).2 * B.σ (u (e.symm j).2)) := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [this, LinearMap.map_smul, smul_eq_mul]; ring
  rw [h2, Matrix.det_submatrix_equiv_self, _root_.GlobalTheory.det_traceGram_blockMatrix w H (fun l => K'.c (w l))]
  by_cases hH0 : H.det = 0
  · rw [hH0, Algebra.norm_zero, mul_zero]; simp [UQ.eta, val]
  have hN : Algebra.norm K.E H.det ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]; exact hH0
  unfold UQ.eta
  rw [val_mul_of_ne (pow_ne_zero _ hw0) hN, val_pow_of_ne hw0, hwv, _root_.GlobalTheory.UnitLemma.Unr.NormVal.normval K K' d φ hU hd0, mul_zero, zero_add,
    zpow_mul]
  rw [zpow_natCast, hd.neg_one_pow]

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_sub_lin_le (w : ℚ_[l]) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    ‖w ^ k - 1 - k * (w - 1)‖ ≤ ‖w - 1‖ ^ 2 := by
  first
  | exact @_root_.GlobalTheory.UltrametricPowerBound.main
  | exact _root_.GlobalTheory.UltrametricPowerBound.main
  | (apply _root_.GlobalTheory.UltrametricPowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricPowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricPowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricPowerBound.main ..)

theorem exists_nat_norm_sub_le (x : ℚ_[l]) (hx : ‖x‖ ≤ 1) :
    ∃ k : ℕ, ‖x - k‖ ≤ (l : ℝ) ^ (-1 : ℤ) := by
  let y : ℤ_[l] := ⟨x, hx⟩
  refine ⟨y.appr 1, ?_⟩
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).2 (y.appr_spec 1)
  rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h
  simpa using h

theorem norm_pow_pow_sub_one (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (b : ℕ) :
    ‖u ^ (l ^ b) - 1‖ = (l : ℝ) ^ (-((j + b : ℕ) : ℤ)) := by
  have hl : l.Prime := Fact.out
  have h := _root_.GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l j hj u hu ((l ^ b : ℕ) : ℤ) (by exact_mod_cast pow_ne_zero _ hl.ne_zero)
  rw [zpow_natCast, padicValInt.of_nat, padicValNat.prime_pow] at h
  rw [h]; push_cast; rfl

theorem exists_norm_sub_pow_le (j : ℕ) (hj : Lev l j) (u s : ℚ_[l]) (hu1 : ‖u‖ = 1)
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (hs : ‖s - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) (m : ℕ) :
    ∃ a : ℕ, ‖s - u ^ a‖ ≤ (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  induction m with
  | zero => exact ⟨0, by simpa using hs⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    set w := u ^ (l ^ m) with hw
    have hw1 : ‖w‖ = 1 := by rw [hw, norm_pow, hu1, one_pow]
    have hd : ‖w - 1‖ = (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) := norm_pow_pow_sub_one j hj u hu m
    have hdpos : 0 < ‖w - 1‖ := by rw [hd]; positivity
    have hd0 : w - 1 ≠ 0 := norm_pos_iff.1 hdpos
    set t := u ^ a with ht
    have ht1 : ‖t‖ = 1 := by rw [ht, norm_pow, hu1, one_pow]
    have ht0 : t ≠ 0 := norm_pos_iff.1 (by rw [ht1]; exact one_pos)
    obtain ⟨k, hk⟩ := exists_nat_norm_sub_le ((s - t) / (t * (w - 1))) (by
      rw [norm_div, norm_mul, ht1, one_mul, div_le_one hdpos, hd]; exact ha)
    refine ⟨a + l ^ m * k, ?_⟩
    have h : s - u ^ (a + l ^ m * k) = t * (w - 1) * ((s - t) / (t * (w - 1)) - k)
        + -(t * (w ^ k - 1 - k * (w - 1))) := by
      rw [pow_add, pow_mul, ← hw, ← ht]
      field_simp
      ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_mul, ht1, one_mul, hd]
      calc _ ≤ (l : ℝ) ^ (-((j + m : ℕ) : ℤ)) * (l : ℝ) ^ (-1 : ℤ) := by gcongr
        _ = _ := by
          rw [← zpow_add₀ hl0.ne']; congr 1; push_cast; ring
    · rw [norm_neg, norm_mul, ht1, one_mul]
      refine (norm_pow_sub_lin_le w hw1.le k).trans ?_
      rw [hd, ← zpow_natCast, ← zpow_mul]
      apply zpow_le_zpow_right₀ hl1.le
      have := hj.1
      push_cast; omega

theorem cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base (K : FinExt l) (j : ℕ) : Gj K j ≤ (K0 K).fixingSubgroup :=
  fun _ hg x => hg ⟨x.1, (le_sup_left : K0 K ≤ Ks K j) x.2⟩

theorem gen_dense : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → (∃ g, IsGen χ K j g) ∧ ∀ g, IsGen χ K j g → ((∀ b : ℕ, IsGen χ K (j + b) (g ^ (l ^ b))) ∧ (∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n) ∧ (Gj K j : Set (GQ l)) ⊆ closure {x | ∃ h ∈ Hinf K, ∃ a : ℕ, x = h * g ^ a}) := by
  intro l _ act χ _ hχ K j hj
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hn, hcont, hG⟩ := _root_.GlobalTheory.Cyc.cyc_basic l χ hχ
  refine ⟨?_, fun g hg => ?_⟩
  · have hp : ‖(l : ℚ_[l]) ^ j‖ = (l : ℝ) ^ (-(j : ℤ)) := by
      rw [norm_pow, Padic.norm_p]; simp
    have hlt : ‖(l : ℚ_[l]) ^ j‖ < 1 := by
      rw [hp]; apply zpow_lt_one_of_neg₀ hl1; have := hj.1; omega
    have hu : ‖(1 : ℚ_[l]) + (l : ℚ_[l]) ^ j‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'),
        norm_one, max_eq_left hlt.le]
    obtain ⟨g, hg0, hg⟩ := (_root_.GlobalTheory.Cyc.finrank_Ks_and_chi_surjective l K).2 χ hχ _ hu
    have : ‖(χ g : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by rw [hg, add_sub_cancel_left, hp]
    exact ⟨g, ((hG K g hg0).1 j).2 this.le, this⟩
  have hg0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K j hg.1
  have hcos : ∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n := by
    intro σ hσ n
    have hσ0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K j hσ
    obtain ⟨a, ha⟩ := exists_norm_sub_pow_le j hj _ _ (hn g) hg.2 (((hG K σ hσ0).1 j).1 hσ) n
    refine ⟨a, ((hG K _ (mul_mem hσ0 (inv_mem (pow_mem hg0 a)))).1 n).2 ?_⟩
    have h0 : (χ g : ℚ_[l]) ≠ 0 := Units.ne_zero _
    have h : ((χ (σ * (g ^ a)⁻¹) : ℚ_[l]ˣ) : ℚ_[l]) - 1
        = ((χ σ : ℚ_[l]) - (χ g : ℚ_[l]) ^ a) / (χ g : ℚ_[l]) ^ a := by
      simp only [map_mul, map_inv, map_pow, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val]
      field_simp
    rw [h, norm_div, norm_pow, hn, one_pow, div_one]
    refine ha.trans (zpow_le_zpow_right₀ hl1.le ?_)
    push_cast; omega
  refine ⟨fun b => ?_, hcos, fun σ hσ => ?_⟩
  · have : ‖(χ (g ^ (l ^ b)) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-((j + b : ℕ) : ℤ)) := by
      rw [map_pow, Units.val_pow_eq_pow_val]
      exact norm_pow_pow_sub_one j hj _ hg.2 b
    exact ⟨((hG K _ (pow_mem hg0 _)).1 _).2 this.le, this⟩
  · rw [mem_closure_iff]
    intro U hU hσU
    have hW : IsOpen (⋃ h ∈ Hinf K, {x : GQ l | h * x⁻¹ * σ ∈ U}) :=
      isOpen_biUnion fun h _ => hU.preimage (by fun_prop)
    have hcl : ∀ n : ℕ, IsClosed (Gj K n : Set (GQ l)) := fun n =>
      InfiniteGalois.fixingSubgroup_isClosed _
    have hanti : Antitone fun n : ℕ => (Gj K n : Set (GQ l)) := by
      intro m n hmn x hx
      have hx0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K n hx
      refine ((hG K x hx0).1 m).2 ((((hG K x hx0).1 n).1 hx).trans
        (zpow_le_zpow_right₀ hl1.le (by omega)))
    have hint : ∀ x ∈ ⋂ n : ℕ, (Gj K n : Set (GQ l)),
        (⋃ h ∈ Hinf K, {x : GQ l | h * x⁻¹ * σ ∈ U}) ∈ nhds x := by
      intro x hx
      rw [Set.mem_iInter] at hx
      have hx0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K 0 (hx 0)
      have hxH : x ∈ Hinf K := by
        refine (hG K x hx0).2.2 (Units.ext ?_)
        rw [Units.val_one, ← sub_eq_zero, ← norm_le_zero_iff]
        by_contra hne
        obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one (not_le.1 hne) (inv_lt_one_of_one_lt₀ hl1)
        have := ((hG K x hx0).1 n).1 (hx n)
        rw [zpow_neg, zpow_natCast, ← inv_pow] at this
        linarith
      exact hW.mem_nhds (Set.mem_biUnion hxH (by simpa using hσU))
    obtain ⟨n, hn'⟩ := exists_subset_nhds_of_compactSpace hanti.directed_ge hcl
      (mem_nhdsSet_iff_forall.2 hint)
    obtain ⟨a, ha⟩ := hcos σ hσ n
    obtain ⟨h, hh, hU'⟩ := Set.mem_iUnion₂.1 (hn' ha)
    refine ⟨h * g ^ a, ?_, h, hh, a, rfl⟩
    simpa [mul_assoc] using hU'

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitLat
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

noncomputable def unitLat (G : Type) [Group G] [TopologicalSpace G] (Qp LL O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] (hO : Function.Injective (algebraMap O LL)) : LocLat G Qp LL O where
  V := LL
  ρ := Representation.trivial LL G LL
  cont := fun x => by simpa using continuous_const
  L :=
    { T := Submodule.span O {1}
      fg := Submodule.fg_span_singleton _
      free := Module.Free.of_equiv
        ((LinearEquiv.ofInjective (LinearMap.toSpanSingleton O LL 1)
          (fun a b h => hO (by simpa [Algebra.smul_def] using h))).trans
          (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range O LL 1).symm))
      span := by
        rw [Submodule.span_span_of_tower, eq_top_iff]
        intro x _
        exact Submodule.mem_span_singleton.2 ⟨x, by simp⟩
      stable := fun g x hx => by simpa using hx }

theorem exists_unitLat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), ∃ one : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), (∀ g x, one.ρ g x = x) ∧ ∃ e : one.V, e ≠ 0 ∧ one.L.T = Submodule.span ↥(OL LL) {e} := by
  intro l _ K LL
  have hO : Function.Injective (algebraMap (↥(OL LL)) ↥LL.1) :=
    Subtype.val_injective
  refine ⟨unitLat (↥(GK K)) ℚ_[l] ↥LL.1 ↥(OL LL) hO, fun _ _ => rfl, (1 : ↥LL.1), ?_, rfl⟩
  show (1 : ↥LL.1) ≠ 0
  exact one_ne_zero

end GlobalTheory.HWL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNeg
section
open NumberField

namespace GlobalTheory

theorem hwAt_conj_swap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) :=
  PI.UnitaryGroupMassFormula.HwConjInf.conjugation_swap

end GlobalTheory
end

