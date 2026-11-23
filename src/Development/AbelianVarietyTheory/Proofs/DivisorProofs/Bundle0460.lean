module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicTensorAcyclicFlatEtaleComplex
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NatCastNeZeroOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0449
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicTensorAcyclicFlatEtaleComplexStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acyclic_tensor_acyclic_flatEtaleComplex : ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T), τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic := by
  first | (exact @GlobalTheory.EtC.acyclic_of_isTensor) | (exact GlobalTheory.EtC.acyclic_of_isTensor) | (intros; apply GlobalTheory.EtC.acyclic_of_isTensor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineFiniteProjectiveRankAtStalk
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AbelianMulFin

theorem affine_finite_projective_rankAtStalk {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (r : ℕ) (hr : ∀ y, f.finrank y = r) (V : Y.Opens)
    (hV : IsAffineOpen V) :
    letI := (f.app V).hom.toAlgebra
    Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
      Module.Projective Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
      ∀ p : PrimeSpectrum Γ(Y, V), Module.rankAtStalk Γ(X, f ⁻¹ᵁ V) p = r := by
  letI := (f.app V).hom.toAlgebra
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have h1 : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := f.finite_app V hV
  have h2 : Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
    have := f.flat_appLE hV hU le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact this
  have h3 : Algebra.FinitePresentation Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
    have := f.finitePresentation_appLE hV hU le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact this
  have h4 := Module.FinitePresentation.of_finite_of_finitePresentation Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
  refine ⟨h1, h2, Module.Flat.projective_of_finitePresentation, fun p => ?_⟩
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ (GlobalTheory.isPullback_fromSpec_app f hV hU) p
  rw [hr] at e
  exact (Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V) p).symm.trans e

theorem isUnit_natCast_Sp {K : Type} [Field K] {n : ℕ} (hn : (n : K) ≠ 0) :
    IsUnit (n : Γ(Spec (CommRingCat.of K), ⊤)) := by
  have := (Ne.isUnit hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  rwa [map_natCast] at this

end GlobalTheory.AbelianMulFin

namespace GlobalTheory.AbelianMulFin

theorem natCast_card_torsion_ne_zero {K : Type} [Field K] {G : Type} [CommGroup G] {n r : ℕ}
    (hn : (n : K) ≠ 0) (hr1 : 1 ≤ r) (hr : r = Nat.card {y : G // y ^ n = 1}) : (r : K) ≠ 0 := by
  intro hr0
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
  · haveI := Fact.mk hp
    have hdvd : ringChar K ∣ r := (CharP.cast_eq_zero_iff K (ringChar K) r).1 hr0
    let H : Subgroup G := (powMonoidHom n : G →* G).ker
    have hHc : Nat.card {y : G // y ^ n = 1} = Nat.card H :=
      Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H, MonoidHom.mem_ker])
    rw [hr, hHc] at hdvd
    have hpos : Nat.card H ≠ 0 := by rw [← hHc, ← hr]; omega
    haveI : Finite H := Nat.finite_of_card_ne_zero hpos
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (ringChar K) hdvd
    have hx2 : (x : G) ^ n = 1 := x.2
    have hxn : x ^ n = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, hx2]; rfl)
    have hd : ringChar K ∣ n := hx ▸ orderOf_dvd_of_pow_eq_one hxn
    exact hn ((CharP.cast_eq_zero_iff K (ringChar K) n).2 hd)
  · have : CharP K 0 := hp ▸ ringChar.charP K
    haveI := CharP.charP_to_charZero K
    exact (Nat.cast_ne_zero.2 (by omega)) hr0

theorem mulA_finite_locallyFree (K : Type) [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [hA : IsAbelianScheme A] (n : ℕ)
    (hn : (n : K) ≠ 0) :
    IsFinite (mulA A n).left ∧ Flat (mulA A n).left ∧ Etale (mulA A n).left ∧
      ∃ r : ℕ, (r : K) ≠ 0 ∧ 1 ≤ r ∧ (∀ a : A.left, (mulA A n).left.finrank a = r) ∧
        ∀ V : A.left.Opens, IsAffineOpen V →
          letI := ((mulA A n).left.app V).hom.toAlgebra
          Module.Finite Γ(A.left, V) Γ(A.left, (mulA A n).left ⁻¹ᵁ V) ∧
          Module.Flat Γ(A.left, V) Γ(A.left, (mulA A n).left ⁻¹ᵁ V) ∧
          Module.Projective Γ(A.left, V) Γ(A.left, (mulA A n).left ⁻¹ᵁ V) ∧
          ∀ p : PrimeSpectrum Γ(A.left, V),
            Module.rankAtStalk Γ(A.left, (mulA A n).left ⁻¹ᵁ V) p = r := by
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.geomConnected
  obtain ⟨⟨hfin, het⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (isUnit_natCast_Sp hn)
  rw [← GlobalTheory.MulLawsCompare.mulN_eq_mulA]
  haveI := hfin
  haveI := het
  haveI : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  let z₀ : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let o : A.left := η[A].left z₀
  have hη : η[A] ≫ mulN A n = η[A] := by
    rw [GlobalTheory.MulLawsCompare.mulN_eq_mulA]
    haveI := GlobalTheory.AbLaw.MulN.isMonHom_mulA A n
    exact IsMonHom.one_hom (mulA A n)
  have hfo : (mulN A n).left o = o := by
    change (η[A].left ≫ (mulN A n).left) z₀ = _
    rw [← Over.comp_left, hη]
  set r := (mulN A n).left.finrank o with hr_def
  have hall : ∀ a, (mulN A n).left.finrank a = r := fun a =>
    (Scheme.Hom.isLocallyConstant_finrank (mulN A n).left).apply_eq_of_preconnectedSpace a o
  have hr1 : 1 ≤ r := by
    have := Scheme.Hom.one_le_finrank_map (mulN A n).left o
    rwa [hfo] at this
  haveI hsurj : Surjective (mulN A n).left :=
    (Scheme.Hom.one_le_finrank_iff_surjective (mulN A n).left).1 fun a => by
      show 1 ≤ (mulN A n).left.finrank a
      rw [hall a]; exact hr1
  have hcard := GlobalTheory.MulLawsCompare.finrank_mulN_eq_card A n (η[A].left) z₀
  refine ⟨hfin, inferInstance, het, r, natCast_card_torsion_ne_zero hn hr1 hcard, hr1, hall,
    fun V hV => affine_finite_projective_rankAtStalk _ r hall V hV⟩

end GlobalTheory.AbelianMulFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfGhostThetaFrobIterValuesXiMuPadic
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open _root_.WittVector

namespace GlobalTheory.PDivLat

section Vals

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_iterate_teichmuller (x : PreTilt O p) (n : ℕ) :
    (WittVector.frobenius : Ainf p O →+* Ainf p O)^[n] (teichmuller p x) =
      teichmuller p (x ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, frobenius_eq_map_frobenius, map_teichmuller,
      frobenius_def, ← pow_mul, ← pow_succ]

theorem ghost_teichmuller (n : ℕ) (x : PreTilt O p) :
    ghost p O n (teichmuller p x) = x.untilt ^ p ^ n := by
  rw [ghost, frobenius_iterate_teichmuller, fontaineTheta_teichmuller, map_pow]

theorem ghost_one (n : ℕ) : ghost p O n 1 = 1 := by
  rw [ghost, iterate_map_one, map_one]

theorem ghost_sub (n : ℕ) (a b : Ainf p O) : ghost p O n (a - b) = ghost p O n a - ghost p O n b := by
  rw [ghost, iterate_map_sub, map_sub]; rfl

theorem ghost_pow (n : ℕ) (a : Ainf p O) (k : ℕ) : ghost p O n (a ^ k) = ghost p O n a ^ k := by
  rw [ghost, iterate_map_pow, map_pow]; rfl

theorem ghost_sum (n : ℕ) (s : Finset ℕ) (f : ℕ → Ainf p O) :
    ghost p O n (∑ i ∈ s, f i) = ∑ i ∈ s, ghost p O n (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ghost_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ghost_add, ih]

theorem frobenius_ofPadic (a : ℤ_[p]) : WittVector.frobenius (ofPadic p O a) = ofPadic p O a := by
  ext k
  rw [coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, map_coeff]
  rw [← map_pow, ZMod.pow_card]

end Vals

theorem ghost_values : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ a, ghost p O 0 a = WittVector.fontaineTheta O p a) ∧ (∀ n a, ghost p O n (ofPadic p O a) = padicToO p O a) ∧ (∀ n, ghost p O n (Sandwich.mu ε) = 0) ∧ ghost p O 0 (xi ε) = 0 ∧ (∀ n, ghost p O (n + 1) (xi ε) = p) ∧ ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε
  have h0 : PreTilt.untilt ε = 1 := hε.zeta_zero
  have h1 : PreTilt.untilt (root ε) ^ p = 1 := by
    have := zeta_succ_pow ε 0
    rw [hε.zeta_zero] at this
    exact this
  have hxi : ∀ n, ghost p O n (xi ε) = ∑ i ∈ Finset.range p, (PreTilt.untilt (root ε) ^ p ^ n) ^ i := by
    intro n
    rw [xi, ghost_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ghost_pow, ghost_teichmuller]
  refine ⟨fun a => rfl, fun n a => ?_, fun n => ?_, ?_, fun n => ?_, fun n a => ?_⟩
  · rw [ghost, Function.iterate_fixed (frobenius_ofPadic a)]
    rfl
  · rw [Sandwich.mu, ghost_sub, ghost_teichmuller, ghost_one, h0, one_pow, sub_self]
  · have hp1 : IsPrimitiveRoot (zeta ε 1) p := by simpa using hε 1
    rw [hxi, pow_zero, pow_one]
    exact hp1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
  · rw [hxi, pow_succ', pow_mul, h1, one_pow]
    simp
  · rw [← ghost_frobenius, GlobalTheory.Dieudonne.frobenius_phiInv]

end GlobalTheory.PDivLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfHodgeTateLatticeConstQpModZpEquiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem ghost_ofPadic (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ) (s : ℤ_[p]) :
    ghost p O n (ofPadic p O s) = padicToO p O s := by
  let g : ℤ_[p] →+* O :=
    { toFun := fun s => ghost p O n (ofPadic p O s)
      map_one' := by simp only [map_one, ghost, iterate_map_one]
      map_mul' := fun a b => by simp only [map_mul, ghost_mul]
      map_zero' := by simp only [map_zero, ghost_zero]
      map_add' := fun a b => by simp only [map_add (f := _), ghost_add] }
  exact congrArg (fun f : ℤ_[p] →+* O => f s) (padicToO_unique p O g)

theorem hodgeTate_constGen (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] :
    hodgeTate (const p O) (constGen p O) = constDlogT p O := by
  rw [hodgeTate_eq_omegaDualMap, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], omegaDualMap_id,
    LinearMap.id_apply]

theorem latt_const_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε),
    ∃ e : latt (const p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, e y = y.1 (constGen p O) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε
  have hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he =>
    IsIdempotentElem.iff_eq_zero_or_one.1 he

  let φ : ℤ_[p] ≃ₗ[ℤ_[p]] (const p O).Tate :=
    LinearEquiv.ofBijective _ (toSpanSingleton_constGen_bijective p O hO)
  have hφ : ∀ s, φ s = s • constGen p O := fun s => rfl
  obtain ⟨eω, heω⟩ := DieudonneSandwich.exists_equiv_constDlogT (p := p) (O := O)
  let f : latt (const p O) →ₗ[Ainf p O] Ainf p O :=
    { toFun := fun y => y.1 (constGen p O)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofBijective f ⟨fun y z h => ?_, fun a => ?_⟩, fun _ => rfl⟩
  · apply Subtype.ext
    apply LinearMap.ext
    intro t
    obtain ⟨s, rfl⟩ := φ.surjective t
    rw [hφ, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    exact congrArg _ h
  · let y : TDual (const p O) :=
      { toFun := fun t => ofPadic p O (φ.symm t) * a
        map_add' := fun t t' => by rw [map_add (f := _), map_add (f := _), add_mul]
        map_smul' := fun c t => by
          rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul, mul_assoc] }
    have hy : y ∈ latt (const p O) := fun n => by
      refine ⟨ghost p O n a • eω.symm.toLinearMap, fun t => ?_⟩
      obtain ⟨s, rfl⟩ := φ.surjective t
      change ghost p O n (ofPadic p O (φ.symm (φ s)) * a) = _
      rw [LinearEquiv.symm_apply_apply, ghost_mul, ghost_ofPadic, hφ,
        hodgeTate_smul (padicToO p O), hodgeTate_constGen, LinearMap.smul_apply,
        LinearEquiv.coe_toLinearMap, map_smul, ← heω, LinearEquiv.symm_apply_apply, smul_eq_mul,
        smul_eq_mul, mul_one, mul_comm]
    refine ⟨⟨y, hy⟩, ?_⟩
    change ofPadic p O (φ.symm (constGen p O)) * a = a
    have : φ.symm (constGen p O) = 1 := φ.symm_apply_eq.2 (by rw [hφ, one_smul])
    rw [this, map_one, one_mul]

end GlobalTheory.PDivLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutEmbInjective
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

noncomputable def autEmb {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) : Emb F :=
  (IsTotallyReal.complexEmbedding_isReal (g.toRingHom.comp ((algebraMap ℝ ℂ).comp i))).embedding

theorem autEmb_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) (y : F) :
    ((autEmb g i y : ℝ) : ℂ) = g ((i y : ℝ) : ℂ) :=
  (IsTotallyReal.complexEmbedding_isReal (g.toRingHom.comp ((algebraMap ℝ ℂ).comp i))).coe_embedding_apply y

theorem autEmb_injective {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) :
    Function.Injective (autEmb (F := F) g) := by
  intro i j h
  ext y
  have h1 : g ((i y : ℝ) : ℂ) = g ((j y : ℝ) : ℂ) := by
    rw [← autEmb_apply, ← autEmb_apply, h]
  exact_mod_cast g.injective h1

theorem aut_perm_emb : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ),
    ∃ π : Equiv.Perm (Emb F), ∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ) := by
  intro F _ _ _ g
  refine ⟨Equiv.ofBijective (autEmb g) (Finite.injective_iff_bijective.mp (autEmb_injective g)), ?_⟩
  intro i y
  exact (autEmb_apply g i y).symm

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIsGaloisTwistedNormGLMulCardGLStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} * Nat.card (GL (Fin n) F) = Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} * Nat.card (GL (Fin n) F') := by
  first | (exact @GlobalTheory.Shin.NormFibre.card_isNorm_mul_card) | (exact GlobalTheory.Shin.NormFibre.card_isNorm_mul_card) | (intros; apply GlobalTheory.Shin.NormFibre.card_isNorm_mul_card  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelwiseEquivalenceIntegralPullback
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem cech_level_eqv_of_integral_pullback :
    ∀ (R : Type) [CommRing R] (F : Shv R) (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X),
    IsPullback a f' f b → IsIntegralHom f →
    (∀ (Z Z' : Scheme.{0}) (h : Z ⟶ X) (h' : Z' ⟶ X') (φ : Z' ⟶ Z), IsIntegralHom h → IsPullback φ h' h b → Eqv R (sch.map φ) F) →
    ∀ (m : GlobalTheory.EtC.cech f' ⟶ GlobalTheory.EtC.cech f), IsPullback m (GlobalTheory.EtC.cechAug f') (GlobalTheory.EtC.cechAug f) (sch.map b) → ∀ n, Eqv R (disc.map (m.app n)) F := by
  intro R _ F Y X Y' X' a f' f b hab hf H m hm n
  have hf' : IsIntegralHom f' := MorphismProperty.of_isPullback (P := @IsIntegralHom) hab hf

  have hn : IsPullback (m.app n) ((GlobalTheory.EtC.cechAug f').app n) ((GlobalTheory.EtC.cechAug f).app n) (yoneda.map b) :=
    hm.map ((evaluation SimplexCategoryᵒᵖ PSh).obj n)
  obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable (@IsIntegralHom) Y X f hf n
  obtain ⟨Z', π', e', hπ', he'⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable (@IsIntegralHom) Y' X' f' hf' n
  have hh : IsIntegralHom (π ≫ f) := inferInstance
  have hh' : IsIntegralHom (π' ≫ f') := inferInstance
  let φ : Z' ⟶ Z := yoneda.preimage (e'.hom ≫ m.app n ≫ e.inv)
  have hφ : yoneda.map φ = e'.hom ≫ m.app n ≫ e.inv := yoneda.map_preimage _
  have hsqY : IsPullback (yoneda.map φ) (yoneda.map (π' ≫ f')) (yoneda.map (π ≫ f)) (yoneda.map b) := by
    refine IsPullback.of_iso hn e'.symm e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hφ]
    · simp [← he']; exact Category.comp_id _
    · simp [← he]; exact Category.comp_id _
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hsq : IsPullback φ (π' ≫ f') (π ≫ f) b := by
    refine IsPullback.of_map yoneda ?_ hsqY
    apply yoneda.map_injective
    simpa using hsqY.w
  have hE := H Z Z' (π ≫ f) (π' ≫ f') φ hh hsq
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  have hdec : disc.map (m.app n) = disc.map e'.inv ≫ sch.map φ ≫ disc.map e.hom := by
    change _ = disc.map e'.inv ≫ disc.map (yoneda.map φ) ≫ disc.map e.hom
    simp only [hφ, ← Functor.map_comp, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hdec]
  exact (hcomp _ _ _ _ _).1 (hiso _ _ (disc.map e'.inv) inferInstance)
    ((hcomp _ _ _ _ _).1 hE (hiso _ _ (disc.map e.hom) inferInstance))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainProductAlexanderWhitneyFormula
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_product_alexander_whitney_formula : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (c : Cochain ((chains R).obj (bidiag.obj (twX E V))) K k) (hc : ∀ (M : ℕ) (s : ℤ) (h : -(M : ℤ) + k = s), c.v (-(M : ℤ)) s h = awZ R (twX E V) M ≫ (crossT V ℓ μ hk α z).v (-(M : ℤ)) s h), μ.IsAW hk ((Cochain.ofHom ((chains R).map (twPi E V))).comp α (zero_add n)) ((Cochain.ofHom ((chains R).map (bidiag.map ℓ ≫ (bidiagConst B).hom))).comp z (zero_add m)) c := by
  first | (exact @GlobalTheory.PBFc.AWCross.isAW_pull_crossT) | (exact GlobalTheory.PBFc.AWCross.isAW_pull_crossT) | (intros; apply GlobalTheory.PBFc.AWCross.isAW_pull_crossT  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainProductVanishingAboveDegree
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_product_vanishing_above_degree : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (p : ℤ) (hα : ∀ c r hr, p < c → α.v c r hr = 0) (c l t : ℤ) (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + k = r) (hc : p < c), (biChains R (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (crossT V ℓ μ hk α z).v t r hr = 0 := by
  first | (exact @GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish) | (exact GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish) | (intros; apply GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFilteredColimitOfEtaleDescent
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ContAlg

theorem cohomology_filteredColimit_of_descent :
    ∀ (M : CommRingCat.{0} ⥤ AbCx) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∀ n, WExact (term M n) (coAug g)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  intro M F0 ι hF0 hι hneg hloc hdesc
  obtain ⟨N, ε, hN, hiso⟩ := GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType AbCx M
  have hterm := (GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN).1
  have hcontN := (GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN).2
  haveI : EtFF.IsStableUnderComposition := GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties.1.1.toIsStableUnderComposition

  have hNneg : ∀ n : ℤ, n < 0 → ∀ A, IsZero ((N.obj A).X n) := by
    intro n hn A
    obtain ⟨J, _, _, D, ιA, ⟨hc⟩, hft⟩ := GlobalTheory.T.exists_filteredColimit_finiteType_int_rings A
    have hel := ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} (term N n)).1 (hterm n)) J D _ hc
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    constructor
    intro x y
    suffices h : ∀ x : (N.obj A).X n, x = 0 by rw [h x, h y]
    intro x
    obtain ⟨j, w, rfl⟩ := hel.1 x
    have hz : IsZero ((N.obj (D.obj j)).X n) := by
      haveI := hiso (D.obj j) (hft j)
      have e : (N.obj (D.obj j)).X n ≅ (M.obj (D.obj j)).X n :=
        (HomologicalComplex.eval _ _ n).mapIso (asIso (ε.app (D.obj j)))
      exact (hneg n hn (D.obj j)).of_iso e
    have : w = 0 := by
      rw [AddCommGrpCat.isZero_iff_subsingleton] at hz
      exact @Subsingleton.elim _ hz _ _
    subst this
    exact map_zero _
  have hqis := GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent CommRingCat.{0} EtFF N M ε
    ⟨0, fun n hn U => ⟨hNneg n hn U, hneg n hn U⟩⟩
    (GlobalTheory.T.coveringsRefine_of_cechConerve_property CommRingCat.{0} EtFF _ (fun A B g hg n =>
      ⟨GlobalTheory.T.coalternatingExact_of_finiteType_iso_filteredColimits (term N n) (term M n) (Functor.whiskerRight ε (HomologicalComplex.eval _ _ n)) (hterm n)
        (fun A' hA' => by
          haveI := hiso A' hA'
          change IsIso ((HomologicalComplex.eval _ _ n).map (ε.app A'))
          infer_instance)
        (fun A' B' g' hg' => hdesc A' B' g' hg' n) A B g hg,
       hdesc A B g hg n⟩))
    (GlobalTheory.T.locallySurjective_of_iso_on_finiteType_approximation N M ε F0 ι hF0 hι hneg hloc hN hiso)
    (GlobalTheory.T.locallyInjective_of_iso_on_finiteType_rings N M ε F0 ι hF0 hι hneg hloc hN hiso)
  exact GlobalTheory.T.filteredColimitCohomology_transport_quasiIso N M ε hqis hcontN

end GlobalTheory.EtC.ContAlg
end

