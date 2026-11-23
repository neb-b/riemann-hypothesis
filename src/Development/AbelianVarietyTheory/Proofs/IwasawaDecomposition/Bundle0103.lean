module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissible
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem.DatLaws


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Mem.DatLaws.dat_ok : ∀ (B : _root_.GlobalTheory.Mem.Base)
    (X : _root_.GlobalTheory.Mem.PreX B.toPre)
    (Ch : _root_.Formalism.L2.Col.Chars B.fields (B.primes X) B.R.m),
    Ch.Ok → Ch.FromHecke B.wts B.embLL →
      (B.dat X Ch).Ok := by
  intro B X Ch hCh hH
  constructor
  case fields => exact _root_.GlobalTheory.Mem.FieldsLaws.fields_ok B
  case fieldsConditions => exact (_root_.GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  case embeddingStarConj => exact _root_.GlobalTheory.Mem.Base.baseData_embedding_conj B X Ch
  case f_eq => exact (_root_.GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).2
  case primes => exact (_root_.GlobalTheory.BasePrimes.primes_ok B X).1
  case piG_cong => exact (_root_.GlobalTheory.BasePrimes.primes_ok B X).2
  case cond => exact _root_.GlobalTheory.Mem.Base.fields_isCond B X
  case chars => exact hCh
  case hecke => exact hH
  case wts => exact _root_.GlobalTheory.Mem.Base.wts_isOk B
  case e_even => exact _root_.GlobalTheory.Mem.Base.dat_e_even B X Ch
  case sizes => exact _root_.GlobalTheory.Mem.Base.primes_sizes B X

end GlobalTheory.Mem.DatLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatOfQuasiFiniteOfFlatFibres
section
open TensorProduct

namespace GlobalTheory

namespace QuasiFiniteFibreFlat

theorem flat_baseChange_trans (S C T D : Type) [CommRing S] [CommRing C] [CommRing T] [CommRing D]
    [Algebra S C] [Algebra S T] [Algebra S D] [Algebra T D] [IsScalarTower S T D]
    [Module.Flat T D] [h : Module.Flat C (C ⊗[S] T)] : Module.Flat C (C ⊗[S] D) := by
  let l := IsScalarTower.toAlgHom S T D
  have hl : (l : T →+* D).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have h1 := (RingHom.flat_algebraMap_iff.mpr h).comp (RingHom.Flat.lTensor (S := S) C hl)
  rw [← RingHom.flat_algebraMap_iff]
  convert h1 using 1
  ext c
  simp

theorem flat_away {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B]
    [hRB : Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Flat A A'] (e : A' ⊗[A] B)
    [Module.Finite A' (Localization.Away e)] : Module.Flat A' (Localization.Away e) := by
  let D := Localization.Away e
  letI : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Flat (A' ⊗[A] B) D := IsLocalization.flat _ (Submonoid.powers e)
  haveI : Algebra.FinitePresentation (A' ⊗[A] B) D := IsLocalization.Away.finitePresentation e
  haveI : Algebra.FinitePresentation A' D := .trans A' (A' ⊗[A] B) D
  haveI : Module.FinitePresentation A' D :=
    Module.FinitePresentation.of_finite_of_finitePresentation A' D
  haveI : Module.Flat R D := by
    have h1 : (algebraMap B (B ⊗[A] A')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    have h2 := h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B))
          (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)
    have h3 := ((RingHom.flat_algebraMap_iff.mpr hRB).comp h2).comp
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (A' ⊗[A] B) D))
    rw [← RingHom.flat_algebraMap_iff]
    convert h3 using 1
    ext r
    rw [IsScalarTower.algebraMap_apply R A' D]
    change algebraMap A' D (algebraMap A A' (algebraMap R A r)) =
      algebraMap (A' ⊗[A] B) D (1 ⊗ₜ algebraMap R B r)
    rw [IsScalarTower.algebraMap_apply A' (A' ⊗[A] B) D, IsScalarTower.algebraMap_apply R A B,
      Algebra.TensorProduct.algebraMap_apply]
    congr 1
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
  refine FinitePresFibreFlat.flat_of_flat_fibres (R := R) (A := A') (B := D)
    fun k C _ _ _ t h w => ?_
  letI : Algebra A C := ((algebraMap A' C).comp (algebraMap A A')).toAlgebra
  haveI : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq' rfl
  haveI := H k C t h w
  haveI : Module.Flat C (C ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A A' C C B)
  exact flat_baseChange_trans A' C (A' ⊗[A] B) D

end QuasiFiniteFibreFlat

theorem flat_of_quasiFinite_of_flat_fibres :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B] [Algebra.QuasiFinite A B] [Module.Flat R B], (∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C), (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) → Module.Flat A B := by
  intro R A B _ _ _ _ _ _ _ _ _ _ H
  refine Module.flat_of_isLocalized_maximal B B (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap B _) fun Q _ => ?_
  obtain ⟨A', _, _, _, P, _, _, e, -, Q', _, _, hQ, he, -, hfin, -⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (Q.under A) Q
  let T := A' ⊗[A] B
  let D := Localization.Away e
  have hD : Module.Flat A' D := QuasiFiniteFibreFlat.flat_away H A' e
  let i : B →+* T := Algebra.TensorProduct.includeRight.toRingHom
  have hi : i.Flat := by
    have h1 : (algebraMap B (B ⊗[A] A')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    exact h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B))
          (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)
  let β := Localization.localRingHom Q Q' i hQ.symm
  have hβ : β.Flat := RingHom.Flat.localRingHom hi Q' Q hQ.symm
  have hle : Submonoid.powers e ≤ Q'.primeCompl := by
    rw [Submonoid.powers_le]; exact he
  letI : Algebra D (Localization.AtPrime Q') :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  haveI : IsScalarTower T D (Localization.AtPrime Q') :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI := IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q') _ _ hle
  have hDQ : Module.Flat D (Localization.AtPrime Q') :=
    IsLocalization.flat _ (Q'.primeCompl.map (algebraMap T D))
  rw [← RingHom.flat_algebraMap_iff]
  refine ringHom_flat_of_square_of_isLocalHom (α := algebraMap A A') (β := β)
    (φ' := (algebraMap D (Localization.AtPrime Q')).comp (algebraMap A' D)) ?_
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hβ
    ((RingHom.flat_algebraMap_iff.mpr hD).comp (RingHom.flat_algebraMap_iff.mpr hDQ))
  ext a
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q), Localization.localRingHom_to_map,
    IsScalarTower.algebraMap_apply A' T D, ← IsScalarTower.algebraMap_apply T D]
  congr 1
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.FinOrder

variable {L : Type} [Field L] [NumberField L]

theorem exists_pow_congr (v : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : (v.adicCompletion L)ˣ, Formalism.L2.Host.IsUnitAt v x →
      Valued.v (((x ^ m : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have hu : Valued.v ((Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    Formalism.L2.Host.unif_spec v
  have hc : Valued.v (((Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hu, ← WithZero.exp_nsmul]; simp
  have hc1 : ((Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hc, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  let c : v.adicCompletionIntegers L := ⟨_, hc1⟩
  have hc0 : c ≠ 0 := fun h => pow_ne_zero n (Units.ne_zero _) (congrArg Subtype.val h)
  have : Finite (v.adicCompletionIntegers L ⧸ Ideal.span {c}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  refine ⟨Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ, Nat.card_pos, fun x hx => ?_⟩
  have hx : Valued.v (x : v.adicCompletion L) = 1 := hx
  have hx' : Valued.v ((x⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  let y : (v.adicCompletionIntegers L)ˣ :=
    ⟨⟨x, hx.le⟩, ⟨(x⁻¹ : (v.adicCompletion L)ˣ), hx'.le⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩
  have h1 := pow_card_eq_one' (x := Units.map (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom y)
  have h2 : Ideal.Quotient.mk (Ideal.span {c})
      ((y : v.adicCompletionIntegers L) ^ Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ) =
      Ideal.Quotient.mk (Ideal.span {c}) 1 := by
    rw [map_pow, map_one]
    exact congrArg Units.val h1
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h2)
  have h3 : (a : v.adicCompletion L) * ((Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n =
      (x : v.adicCompletion L) ^ Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ - 1 :=
    congrArg Subtype.val ha
  rw [Units.val_pow_eq_pow_val, ← h3, map_mul, hc]
  exact mul_le_of_le_one_left' a.2

theorem triv_inf (χ : Formalism.L2.Host.HChar L) (h : ∀ k, χ.inf k = 1) (u : ∀ w : InfinitePlace L, (w.Completion)ˣ) :
    χ.1 (∏ w, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (u w)) = 1 := by
  have key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => χ.1 (∏ w, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (u w))) = fun _ => 1 := by
    refine (GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer ?_ continuous_const ?_
    · exact χ.2.1.comp (continuous_finsetProd _ fun w _ =>
        (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continuous_apply w))
    · funext k
      have h1 : χ.1 (Formalism.L2.Host.infDiag k) = 1 := h k
      unfold Formalism.L2.Host.infDiag at h1
      rw [MonoidHom.finsetProd_apply] at h1
      exact h1
  exact congrFun key u

theorem exists_decomp (a : Neutral.B1.Ideles L) :
    ∃ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, a = (∏ w, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (u w)) * finPartI L a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    (Pi.evalMonoidHom (fun w : InfinitePlace L => w.Completion) w).comp
      (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
  let q : AdeleRing (𝓞 L) L →* FiniteAdeleRing (𝓞 L) L :=
    MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  refine ⟨fun w => Units.map (p w) a, Units.ext (Prod.ext (funext fun w => ?_) ?_)⟩
  · show p w a = p w ((∏ w, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (Units.map (p w) a)) * finPartI L a : Neutral.B1.Ideles L)
    rw [Units.val_mul, map_mul, Units.coe_prod, map_prod, Finset.prod_eq_single w]
    · show p w a = Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w (p w a) w * 1
      simp
    · intro w' _ hw
      show Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w' (p w' a) w = 1
      exact Pi.mulSingle_eq_of_ne hw.symm _
    · simp
  · show q a = q ((∏ w, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (Units.map (p w) a)) * finPartI L a : Neutral.B1.Ideles L)
    rw [Units.val_mul, map_mul, Units.coe_prod, map_prod, Finset.prod_eq_one, one_mul]
    · rfl
    · exact fun _ _ => rfl


open Classical in
theorem finite_order_of_inf_eq_one : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L),
    (∀ k, χ.inf k = 1) → ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n := by
  intro L _ _ χ h
  obtain ⟨hfin, hlev⟩ := GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level L χ
  have hm : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ x, Formalism.L2.Host.IsUnitAt v x → χ.loc v x ^ m = 1 := by
    intro v
    obtain ⟨n, hn⟩ := hlev v
    obtain ⟨m, hm, hx⟩ := exists_pow_congr v n
    refine ⟨m, hm, fun x hu => ?_⟩
    rw [← map_pow]
    refine hn _ ?_ (hx x hu)
    show Valued.v (((x ^ m : (v.adicCompletion L)ˣ) : v.adicCompletion L)) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hu, one_pow]
  choose m hm0 hm using hm
  set M := ∏ v ∈ hfin.toFinset, m v with hM
  have hM0 : 0 < M := Finset.prod_pos fun v _ => hm0 v
  have hloc : ∀ v x, Formalism.L2.Host.IsUnitAt v x → χ.loc v x ^ M = 1 := by
    intro v x hx
    by_cases hv : χ.UnrAt v
    · rw [hv x hx, one_pow]
    · obtain ⟨d, hd⟩ : m v ∣ M := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hv)
      rw [hd, pow_mul, hm v x hx, one_pow]
  have hunit : ∀ a ∈ unitIdl L, (χ ^ M).1 a = 1 := by
    intro a ha
    obtain ⟨u, hu⟩ := exists_decomp a
    have h1 : (χ ^ M).1 (finPartI L a) = 1 := by
      refine GlobalTheory.Mem.LocTriv.eq_one_of_local L _ (χ ^ M).2.1 _ (finPartI_mem_unitIdl.2 ha) (fun _ => rfl) fun v x hx => ?_
      refine hloc v x ?_
      show Valued.v (x : v.adicCompletion L) = 1
      rw [hx]
      exact ha v
    have h2 : (χ ^ M).1 (∏ w, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (u w)) = 1 := by
      show χ.1 _ ^ M = 1
      rw [triv_inf χ h, one_pow]
    rw [hu, map_mul, h1, h2, one_mul]
  have hle : unitIdl L ⊔ (Neutral.B1.diagUnits L).range ≤ (χ ^ M).1.ker := by
    refine sup_le hunit ?_
    rintro _ ⟨k, rfl⟩
    exact (χ ^ M).2.2 k
  have hfi := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨M * (unitIdl L ⊔ (Neutral.B1.diagUnits L).range).index, Nat.mul_pos hM0 (Nat.pos_of_ne_zero hfi.index_ne_zero), ?_⟩
  unfold Formalism.L2.Host.HChar.OrderDvd
  rw [pow_mul]
  refine Subtype.ext (MonoidHom.ext fun a => ?_)
  show (χ ^ M).1 a ^ _ = 1
  rw [← map_pow]
  exact hle (Subgroup.pow_index_mem _ a)

end GlobalTheory.Mem.FinOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharTrivialOnCongruenceUnitIdeles
section
noncomputable section

open IsDedekindDomain NumberField Filter Topology

namespace GlobalTheory.LevelChars.LevTriv

open Neutral.B1 Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]


open Classical in
theorem prod_localIdele_comp (z : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ)
    (F : Finset (HeightOneSpectrum (𝓞 L))) :
    ((∏ v ∈ F, Neutral.B1.localIdele L v (z v) : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).1 = 1 ∧
    ∀ w, ((∏ v ∈ F, Neutral.B1.localIdele L v (z v) : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 w =
      if w ∈ F then ((z w : (w.adicCompletion L)ˣ) : w.adicCompletion L) else 1 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨rfl, fun w => by simp <;> rfl⟩
  | insert a F ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul]
    have e1 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).1 = x.1 * y.1 := fun _ _ => rfl
    have e2 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).2 = x.2 * y.2 := fun _ _ => rfl
    refine ⟨?_, fun w => ?_⟩
    · rw [e1, ih.1, mul_one]; rfl
    · have e : ∀ x y : FiniteAdeleRing (𝓞 L) L, (x * y) w = x w * y w := fun _ _ => rfl
      rw [e2, e, ih.2 w]
      by_cases hw : w = a
      · subst hw
        rw [localIdele_snd_self, if_neg ha, if_pos (Finset.mem_insert_self _ _), mul_one]
      · rw [(localIdele_isSupportedAt L a (z a)).2 w hw, one_mul]
        by_cases hF : w ∈ F
        · rw [if_pos hF, if_pos (Finset.mem_insert_of_mem hF)]
        · rw [if_neg hF, if_neg (fun h => (Finset.mem_insert.1 h).elim hw hF)]

theorem tendsto_prod_localIdele (z : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ) (hz : ∀ v, Formalism.L2.Host.IsUnitAt v (z v))
    (c : Neutral.B1.Ideles L) (hc1 : (c : AdeleRing (𝓞 L) L).1 = 1)
    (hc2 : ∀ v, (c : AdeleRing (𝓞 L) L).2 v = ((z v : (v.adicCompletion L)ˣ) : v.adicCompletion L)) :
    Tendsto (fun F : Finset (HeightOneSpectrum (𝓞 L)) => ((∏ v ∈ F, Neutral.B1.localIdele L v (z v) : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L))
      atTop (𝓝 (c : AdeleRing (𝓞 L) L)) := by
  classical
  let A : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w => w.adicCompletionIntegers L
  have hA : ∀ w, ((z w : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈ A w := fun w => (hz w).le
  let g : Finset (HeightOneSpectrum (𝓞 L)) → ∀ w, A w := fun F w =>
    if w ∈ F then ⟨_, hA w⟩ else ⟨1, one_mem (w.adicCompletionIntegers L)⟩
  let o : ∀ w, A w := fun w => ⟨_, hA w⟩
  have hg : Tendsto g atTop (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {w}] with F hF
    have hw : w ∈ F := hF (Finset.mem_singleton_self w)
    simp only [g, o, if_pos hw]
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  have h3 : Tendsto (fun F : Finset (HeightOneSpectrum (𝓞 L)) =>
      ((∏ v ∈ F, Neutral.B1.localIdele L v (z v) : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2) atTop (𝓝 (c : AdeleRing (𝓞 L) L).2) := by
    have eo : RestrictedProduct.structureMap _ A cofinite o = (c : AdeleRing (𝓞 L) L).2 := by
      apply Subtype.ext; funext w; exact (hc2 w).symm
    rw [← eo]
    refine Tendsto.congr (fun F => ?_) h2
    apply Subtype.ext; funext w
    show ((g F w : A w) : w.adicCompletion L) = _
    refine Eq.trans ?_ ((prod_localIdele_comp z F).2 w).symm
    by_cases hw : w ∈ F
    · simp only [g, if_pos hw]
    · simp only [g, if_neg hw]
  have h4 := (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h3
  have ec : (c : AdeleRing (𝓞 L) L) = ((1 : InfiniteAdeleRing L), (c : AdeleRing (𝓞 L) L).2) := Prod.ext hc1 rfl
  rw [ec]
  refine Tendsto.congr (fun F => ?_) h4
  exact Prod.ext (prod_localIdele_comp z F).1.symm rfl

theorem eq_one_fin (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L) (hU : ∀ v, v ∉ S → ψ.UnrAt v)
    (hN : ∀ v ∈ S, ψ.LevelLe v N) (f : Neutral.B1.Ideles L) (hf1 : (f : AdeleRing (𝓞 L) L).1 = 1)
    (hf : f ∈ GlobalTheory.LevelChars.levSub L S N) : ψ.1 f = 1 := by
  classical
  let u : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ := fun v =>
    ⟨(f : AdeleRing (𝓞 L) L).2 v, ((f⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 v,
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) f.mul_inv,
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) f.inv_mul⟩
  have hu : ∀ v, Formalism.L2.Host.IsUnitAt v (u v) := fun v => (hf v).1
  have hui : ∀ v, Formalism.L2.Host.IsUnitAt v (u v)⁻¹ := fun v => by
    unfold Formalism.L2.Host.IsUnitAt
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu v, inv_one]
  have hloc : ∀ v, ψ.1 (Neutral.B1.localIdele L v (u v)) = 1 := fun v => by
    by_cases hv : v ∈ S
    · exact hN v hv (u v) (hu v) ((hf v).2 hv)
    · exact hU v hv (u v) (hu v)
  let b : Finset (HeightOneSpectrum (𝓞 L)) → Neutral.B1.Ideles L := fun F => ∏ v ∈ F, Neutral.B1.localIdele L v (u v)
  have hb1 : ∀ F, ψ.1 (b F) = 1 := fun F => by
    simp only [b, map_prod]
    exact Finset.prod_eq_one fun v _ => hloc v
  have hfi1 : ((f⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := by
    have h := congrArg (fun y : AdeleRing (𝓞 L) L => y.1) f.inv_mul
    have e1 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).1 = x.1 * y.1 := fun _ _ => rfl
    simp only [e1, hf1, mul_one] at h
    exact h
  have t1 := tendsto_prod_localIdele u hu f hf1 fun v => rfl
  have t2 := tendsto_prod_localIdele (fun v => (u v)⁻¹) hui f⁻¹ hfi1 fun v => rfl
  have tb : Tendsto b atTop (𝓝 f) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine t1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (Tendsto.congr (fun F => ?_) t2))
    show ((∏ v ∈ F, Neutral.B1.localIdele L v (u v)⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L) = (((b F)⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L)
    congr 1
    simp only [b, map_inv, Finset.prod_inv_distrib]
  have t3 := (ψ.2.1.tendsto f).comp tb
  have t4 : Tendsto (ψ.1 ∘ b) atTop (𝓝 1) := tendsto_const_nhds.congr fun F => (hb1 F).symm
  exact tendsto_nhds_unique t3 t4

theorem infIdele_mem (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (x : (InfiniteAdeleRing L)ˣ) :
    GlobalTheory.HeckeSplit.infIdele L x ∈ GlobalTheory.LevelChars.levSub L S N := fun v => by
  have e : GlobalTheory.LevelChars.compAt L v (GlobalTheory.HeckeSplit.infIdele L x) = 1 := rfl
  refine ⟨by rw [e, map_one], fun _ => ?_⟩
  rw [e, sub_self, map_zero]
  exact zero_le

theorem infDiag_eq_infIdele (k : Lˣ) :
    Formalism.L2.Host.infDiag k = GlobalTheory.HeckeSplit.infIdele L (Units.map (algebraMap L (InfiniteAdeleRing L)).toMonoidHom k) := by
  classical
  apply Units.ext
  show ((Formalism.L2.Host.infDiag k : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1)
  unfold Formalism.L2.Host.infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

theorem eq_one_inf (ψ : Formalism.L2.Host.HChar L) (hinf : ∀ k : Lˣ, ψ.inf k = 1) (x : (InfiniteAdeleRing L)ˣ) :
    ψ.1 (GlobalTheory.HeckeSplit.infIdele L x) = 1 := by
  have hc : Continuous (GlobalTheory.HeckeSplit.infIdele L) :=
    Continuous.units_map _ (continuous_id.prodMk continuous_const)
  refine (GlobalTheory.HeckeGal.denseRange_units_inf L).induction_on x
    (isClosed_eq (ψ.2.1.comp hc) continuous_const) fun k => ?_
  rw [← infDiag_eq_infIdele]
  exact hinf k

theorem levSub_triv : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (ψ : Formalism.L2.Host.HChar L), (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) →
    ∀ a ∈ GlobalTheory.LevelChars.levSub L S N, ψ.1 a = 1 := by
  intro L _ _ S N ψ hinf hU hN a ha
  set x := GlobalTheory.HeckeSplit.infPart L a
  have hdec : a = GlobalTheory.HeckeSplit.infIdele L x * ((GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a) := by
    rw [mul_inv_cancel_left]
  have hf1 : (((GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := by
    rw [← map_inv]
    show ((a⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).1 * (a : AdeleRing (𝓞 L) L).1 = 1
    have h := congrArg (fun y : AdeleRing (𝓞 L) L => y.1) a.inv_mul
    exact h
  have hmem : (GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a ∈ GlobalTheory.LevelChars.levSub L S N :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (infIdele_mem S N x)) ha
  rw [hdec, map_mul, eq_one_inf ψ hinf x, eq_one_fin S N ψ hU hN _ hf1 hmem, mul_one]

end GlobalTheory.LevelChars.LevTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTwistOfIsDelta
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem IsTwist.mul_twist {S : Set ℕ} {ξ ξ' : Formalism.L2.Host.HChar H.E} (h : IsTwist H S ξ) (h' : IsTwist H S ξ') :
    IsTwist H S (ξ * ξ') := by
  obtain ⟨⟨n, hn, ho⟩, ht, hl, hr⟩ := h
  obtain ⟨⟨n', hn', ho'⟩, ht', hl', hr'⟩ := h'
  refine ⟨⟨n * n', Nat.mul_pos hn hn', ?_⟩, ht.mul ht', fun v => Formalism.L2.Host.HChar.LevelLe.mul (hl v) (hl' v), fun v hv => ?_⟩
  · unfold Formalism.L2.Host.HChar.OrderDvd at *
    rw [mul_pow, pow_mul, ho, one_pow, one_mul, mul_comm n n', pow_mul, ho', one_pow]
  · by_cases h1 : ξ.UnrAt v
    · exact hr' v fun h2 => hv (h1.mul h2)
    · exact hr v h1

theorem isTwist_of_isDelta {S : Set ℕ} {p : ℕ} {δ : Formalism.L2.Host.HChar H.E} (hp : p.Prime) (hs : SplitsC H.E p) (hS : p ∉ S)
    (h : Formalism.L2.Host.IsDelta (H := H) p δ) : IsTwist H S δ := by
  refine ⟨h.fin, h.triv, h.tame, fun v hv => ?_⟩
  have hv' : Formalism.L2.Host.OverP H p v := by
    by_contra hn
    exact hv (h.unr v hn)
  obtain ⟨h1, h2, h3, -⟩ := splitsC_main R H p hp hs v hv'
  rw [h1]
  exact ⟨h3, hp, h2, hS⟩

end GlobalTheory.Mem.Chr
end

