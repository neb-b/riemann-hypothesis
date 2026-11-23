module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnitOfIsUniUp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLatInOfIndexLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0386

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceUnitriangularColumnVanishingIdempotentEqSum
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.ExactMult

variable {g : ℕ} [Fact g.Prime]

theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Gn g n → ℂ) :
    wh ψ (fun h => ∑ i ∈ s, f i h) = ∑ i ∈ s, wh ψ (f i) := by
  unfold wh tr
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun h => c * f h) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem wh_gg_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (gg ψ 0) = 1 := by
  have hU : ∀ M : Mt g 0, IsUniUp M := fun M a => a.elim0
  have hgg : ∀ x : Gn g 0, gg ψ 0 x = 1 := by
    intro x
    unfold gg
    simp [hU]
  unfold wh eU
  rw [GlobalTheory.GLm.TraceTail.tr_eDat]
  simp [hU, hgg]

theorem isClass_der (ψ : AddChar (ZMod g) ℂ) {N : ℕ} (i : ℕ) (hi : i ≤ N) (χ : Gn g N → ℂ)
    (hχ : IsClass χ) : IsClass (der ψ i χ) := by
  intro x y
  have h := ((GlobalTheory.GLq.HcClass.hc_class g i (N - i) N (by omega)).2 χ hχ).2
  unfold der
  congr 1
  funext z
  exact h z x y

theorem wh_hc (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ)
    (hα : IsClass α) (hβ : IsClass β) : wh ψ (hc a b α β (a + b)) = wh ψ α * wh ψ β := by
  unfold hc
  rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ a b (a + b) rfl _ (fun y x z => by simp only [hα x z])
    (fun x y z => by simp only [hβ y z])]
  simp only [wh_const_mul]
  rw [show (fun x => α x * wh ψ β) = (fun x => wh ψ β * α x) from funext fun _ => mul_comm _ _,
    wh_const_mul, mul_comm]

end GlobalTheory.GLq.ExactMult

namespace GlobalTheory.GLq.ExactMult

open GlobalTheory.GLm

theorem tr_eJ'_eq_sum_wh_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k : ℕ), 1 ≤ k →
    k < N → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ' g N k ψ) χ =
      (∑ i ∈ Finset.range k, wh ψ (der ψ i χ) * ((g : ℂ) ^ (k - i) - (g : ℂ) ^ (k - i - 1))) +
        wh ψ (der ψ k χ) := by
  intro g _ ψ hψ N k _ hk χ hχ
  rw [tr_eJ'_eq_wh_tail g ψ N k χ hk]
  have hM : IsMirClass χ := fun p x _ _ => hχ x p
  have hF := GlobalTheory.GLm.TailClass.isMirClass_tail g ψ (k + 1) N χ (by omega) (by omega) hM
  rw [show (fun h => tail ψ (k + 1) χ (diag1 h (k + 1))) = fun h =>
      ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i (tail ψ (k + 1) χ)) (gg ψ (k - i)) k h from
    funext (mirClass_diag1_eq_sum g ψ hψ k _ hF)]
  rw [wh_sum, Finset.sum_range_succ]
  have key : ∀ i, i < k + 1 → wh ψ (hc i (k - i) (der ψ i (tail ψ (k + 1) χ)) (gg ψ (k - i)) k) =
      wh ψ (der ψ i χ) * wh ψ (gg ψ (k - i)) := by
    intro i hi
    rw [GlobalTheory.GLm.DerTail.der_tail g ψ i (k + 1) N χ hi (by omega)]
    have := wh_hc ψ hψ i (k - i) (der ψ i χ) (gg ψ (k - i)) (isClass_der ψ i (by omega) χ hχ)
      (GlobalTheory.GLq.GGDeg.gg_one_and_isClass g ψ (k - i)).2
    rwa [show i + (k - i) = k by omega] at this
  rw [key k (by omega), Nat.sub_self, wh_gg_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [key i (by omega), (_root_.GlobalTheory.GLq.GGNorm.gg_norm g ψ hψ (k - i) (by omega)).1]

end GlobalTheory.GLq.ExactMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistModuleAllCharacterPowersOfAdmissible
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.ExportFromInputs

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

open GlobalTheory.TwistInputsTest GlobalTheory.TwAll

theorem twistModule_all_character_powers_of_admissible (bkP : BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (h2 : TwAll.admissibleIndexBoundAllPowers Y bkP N0) (h3 : IsotypicPartsInternalDirectSum Y E)
    (h5 : GroupAlgebraIntegrality Y) (h7 : admT4 Y E) (h10 : TwistedSeriesSpecialisation Y) (h11 : GoodLatticePoints Y) (i : X.Tw) (hi : X.NonzeroIndexPlace i) :
    TwAll.goodTwistExistsAllCoprimePowers Y bkP E N0 i := by
  classical
  intro hs eps' he hF S hS A
  choose z hz using fun b => (h5 i hi b).1
  have hAB := fun j hj b => abHyp_fam Y E i hi j hj b z (hz b) S h3 h5 h11 (hF j hj b) (hS j hj b)
  obtain ⟨Q, k, ψ₀, hall⟩ := h2 i hi hs eps' he (fam Y i z S) hAB (levs Y i S ∪ A)
  refine ⟨Q, k, ψ₀, fun n hn => ?_⟩
  have hn' := hall n hn
  generalize ψ₀ ^ n = ψ' at hn' ⊢
  obtain ⟨hok, ha, hc, hd, M, χ, hχ, epsB, h0, hsum, H⟩ := hn'
  have key : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, _ := fun j hj b => by
    obtain ⟨htw, hu, hdis⟩ := twOK_of_psiOk i _ Q k ψ' hok b
    refine export_at Y E i hi j hj b (S j b) h3 h7 (hF j hj b) (hS j hj b) k Q _ htw hu (epsB j b) ?_
    intro T hT hle
    obtain ⟨-, hfg, hsp, -⟩ := h3 i hi j hj b
    have hA : (fam Y i z S).A j b = AO Y i j b := zO_eq Y i j b _ (hz b)
    have hTh : (fam Y i z S).Th j b = (Th Y i j b (SgJ Y E i j b)).map (AO Y i j b) := by
      rw [← (hS j hj b).2.2, RFam.Th, hA]; rfl
    rw [← hTh]
    refine H j hj b T ?_ fun a ha => ?_
    · have : Submodule.span (FractionRing (X.O i)) ((fam Y i z S).B j b : Set (Y.Fm i j b)) = V0 Y i j b :=
        span_of_isLatIn (isLatIn_B Y i j b hfg hsp)
      rw [this]; exact hT
    · have ha' : a ∈ S j b := ha
      rw [hχ, psiAt_comp] at htw hle
      have hlev : Disjoint Q (Y.lev i j b a) := by
        refine hdis.mono_right (le_trans ?_ Finset.subset_union_left)
        intro v hv
        simp only [levs, Finset.mem_biUnion]
        exact ⟨j, hj, b, Finset.mem_univ _, a, ha', hv⟩
      rw [hA]
      refine hle ⟨_, ?_, rfl⟩
      refine Submodule.span_mono ?_ (h10 i hi j hj b k Q M _ htw a hlev)
      exact Set.biUnion_subset_biUnion_left (Set.singleton_subset_iff.2 ((hS j hj b).1 ha'))
  exact ⟨hok, ⟨epsB, h0, hsum, fun j hj b => (key j hj b).1⟩, fun j hj b => (key j hj b).2, ha, hc, hd⟩

end GlobalTheory.ExportFromInputs


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroup
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.SmallActs

theorem toZModPow_cycZ_eq_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (n : ℕ) (σ : G F Ω) (hσ : ∀ ζ : Ω, ζ ^ (l ^ n) = 1 → σ ζ = ζ) :
    PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hspec : σ ζ = ζ ^ (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) ζ hζ.pow_eq_one
  rw [hσ ζ hζ.pow_eq_one] at hspec
  set m := (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])).val with hm
  have heq' : (hζ.isUnit hN0).unit ^ m = (hζ.isUnit hN0).unit ^ 1 := Units.ext (by simpa using hspec.symm)
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
  rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])), ← hm,
    (ZMod.natCast_eq_natCast_iff _ _ _).2 heq', Nat.cast_one]

theorem map_eq_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (T : Matrix (Fin r) (Fin r) O)
    (h : ∀ a b, algebraMap O A ((T - 1) a b) = 0) : T.map (algebraMap O A) = 1 := by
  ext a b
  have := h a b
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem repOn_of_map_eq_one {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ}
    (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ) (Y : Type) [AddCommGroup Y] [Module A Y] (g : Γ)
    (h : (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A) = 1) (m : Fin r → Y) :
    repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m := by
  change (((κ g : Aˣ) : A) • matAct ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A))) m = _
  rw [h, matAct_one]
  rfl

theorem small_acts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y], ∀ g ∈ L, (∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Aˣ) : A) • m) ∧ (∀ m, repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m) ∧ cycMod D.host.E N.Om (X.l i) (nu X i + 1) g = 1 := by
  intro D N X i s _ M L z hM hS A _ _ κ ρ hK hρ Y _ _ g hg
  have hT : ∀ g ∈ L, (Tmat i s g).map (algebraMap (X.O0 i) A) = 1 := fun g hg =>
    map_eq_one _ fun a b => hK _ (hS.2.2 g hg a b)
  have hc : PadicInt.toZModPow (nu X i + 1) ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) = 1 := by
    refine toZModPow_cycZ_eq_one (nu X i + 1) g fun ζ hζ => hS.2.1 g hg ζ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hM
    have e : 2 * X.l i ^ M = X.l i ^ (nu X i + 1) * (2 * X.l i ^ k) := by rw [hk, pow_add (X.l i) (nu X i + 1) k]; ring
    rw [e, pow_mul, hζ, one_pow]
  refine ⟨repOn_of_map_eq_one _ κ Y g (by rw [Tgl_coe]; exact hT g hg), repOn_of_map_eq_one _ κ Y g ?_, Units.ext hc⟩
  have hmem : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
    intro h
    have h2 := h.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at h2
    exact X.O_l i h2
  have he : algebraMap (X.O0 i) A ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1 := by
    have h1 : ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) - 1 ∈
        RingHom.ker (PadicInt.toZModPow (nu X i + 1) : ℤ_[X.l i] →+* ZMod (X.l i ^ (nu X i + 1))) := by
      rw [RingHom.mem_ker, map_sub, hc, map_one, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
    obtain ⟨c, h1⟩ := h1
    change algebraMap (X.O0 i) A (algebraMap ℤ_[X.l i] (X.O0 i) (cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ)) = 1
    have h2 : algebraMap (X.O0 i) A ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i)) = 0 :=
      hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hmem)
    rw [sub_eq_iff_eq_add.1 h1, map_add (f := _), map_add (f := _), map_one, map_one, map_mul, map_pow, map_natCast, pow_succ, map_mul, h2,
      zero_mul, zero_add]
  have hinv : (Tmat i s g)⁻¹ = Tmat i s g⁻¹ := by
    rw [← Tgl_coe, ← Tgl_coe, map_inv, Matrix.coe_units_inv]
  rw [hρ g, Tdual, hinv]
  ext a b
  have := congrFun (congrFun (hT g⁻¹ (L.inv_mem hg)) b) a
  rw [Matrix.map_apply] at this
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, he, one_mul, Matrix.transpose_apply, this,
    Matrix.one_apply, Matrix.one_apply]
  simp only [eq_comm]

end GlobalTheory.NewPrime.SmallActs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSection
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PendOf.PrTypeProof

theorem typeSum_indep (D : D7) (i : D.nd.Loc) : iSupIndep (typeSum D i) := by
  intro o
  have hd : Disjoint {P | D.naut.ptV i P = o} {P | D.naut.ptV i P ≠ o} :=
    Set.disjoint_left.2 fun P h h' => h' h
  refine ((D.naut.typeV_indep i).disjoint_biSup_biSup hd).mono_right ?_
  refine iSup₂_le fun o' ho' => iSup₂_le fun P hP => ?_
  exact le_biSup (D.naut.typeV i) (show P ∈ {P | D.naut.ptV i P ≠ o} from fun e => ho' (hP.symm.trans e))

theorem typeV_le_typeSum (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) :
    D.naut.typeV i P ≤ typeSum D i (D.naut.ptV i P) :=
  le_biSup (D.naut.typeV i) (show P ∈ {Q | D.naut.ptV i Q = D.naut.ptV i P} from rfl)

theorem main : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → PrType D := by
  intro D hS i PI x hx
  classical
  let s := (hS i).some
  set v := D.nd.prMt i x with hvdef
  have hvtop : v ∈ ⨆ y, heckeEig (D.nd.T i) (D.nd.act i) y := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ v).1 hvtop
  have hΦv : s.Φ v = ∑ y ∈ f.support, s.Φ (f y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, Finsupp.sum, map_sum]
  have hn := s.split x
  have hind := typeSum_indep D i
  have hjx : D.what₂.jMt _ _ x ∈ typeSum D i (D.naut.ptV i PI) := typeV_le_typeSum D i PI hx
  have key : ∀ y, some y ≠ D.naut.ptV i PI → f y = 0 := by
    intro y hy
    by_cases hs : y ∈ f.support
    · have e : s.Φ (f y) = (D.what₂.jMt _ _ x - (D.what₂.jMt _ _ x - s.Φ v)) -
          ∑ y' ∈ f.support.erase y, s.Φ (f y') := by
        rw [sub_sub_cancel, hΦv, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : s.Φ (f y) ∈ ⨆ (o) (_ : o ≠ some y), typeSum D i o := by
        rw [e]
        refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) (Submodule.sum_mem _ fun y' hy' => ?_)
        · exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (Ne.symm hy) hjx)
        · exact Submodule.mem_iSup_of_mem none (Submodule.mem_iSup_of_mem (by simp) hn)
        · refine Submodule.mem_iSup_of_mem (some y') (Submodule.mem_iSup_of_mem ?_ (s.eig y' _ (hf y')))
          exact fun e' => Finset.ne_of_mem_erase hy' (Option.some_injective _ e')
      have h0 : s.Φ (f y) = 0 := (Submodule.disjoint_def.1 (hind (some y))) _ (s.eig y _ (hf y)) m2
      exact s.inj (h0.trans (map_zero s.Φ).symm)
    · exact Finsupp.notMem_support_iff.1 hs
  refine ⟨fun p hp => ?_, fun hp => ?_⟩
  · rw [← hsum, Finsupp.sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hyp : y = p
    · subst hyp; exact hf y
    · rw [key y (by rw [hp]; exact fun e => hyp (Option.some_injective _ e))]
      exact Submodule.zero_mem _
  · rw [← hsum, Finsupp.sum]
    exact Finset.sum_eq_zero fun y _ => key y (by rw [hp]; simp)

end GlobalTheory.PendOf.PrTypeProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfDetectingCoboundaryCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_le_of_detects : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Detects p r A B → jumpSum (wild K L) A B ≤ 6 * E := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A B hp hE hord hax hdet
  obtain ⟨j, hinj, hrange, happ, hram⟩ := _root_.GlobalTheory.PMon.Ram.baseChange_fixedField K L A

  have haxF : AxIn (IntermediateField.fixedField A) L p := by
    intro J x hx
    obtain ⟨y, hy, hxy⟩ := hax (J.map j) x (by
      rintro σ ⟨τ, hτ, rfl⟩
      rw [happ]
      exact hx τ hτ)
    refine ⟨y, fun τ hτ => ?_, hxy⟩
    rw [← happ]
    exact hy (j τ) ⟨τ, hτ, rfl⟩
  have hdetF : Detects p r ⊤ (B.comap j) := by
    intro τ₀ _ hτ₀
    have hA : j τ₀ ∈ A := hrange.le (MonoidHom.mem_range.mpr ⟨τ₀, rfl⟩)
    obtain ⟨x, a, hxa, hnd⟩ := hdet (j τ₀) hA hτ₀
    refine ⟨x, fun τ => a (j τ), fun τ _ => ?_, hnd⟩
    obtain ⟨z, hz, hzx⟩ := hxa (j τ) (hrange.le (MonoidHom.mem_range.mpr ⟨τ, rfl⟩))
    refine ⟨z, hz, ?_⟩
    rw [← happ]
    exact hzx
  have key := _root_.GlobalTheory.PMon.Ram.jumpSum_wild_top_le_of_detects (IntermediateField.fixedField A) L p E r (B.comap j) hp hE hord haxF hdetF
  have hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hram _
  rw [hwild, jumpSum_comap_injective _ _ j _ B hinj, hrange] at key
  exact key

end GlobalTheory.PMon.Ram
end

