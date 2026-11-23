module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing Ideal

universe u

variable {R : Type u} [CommRing R]

theorem spanFinrank_maximalIdeal_quotient_add_one_le [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  classical
  set m := maximalIdeal R with hm
  let x' : m := ⟨x, hx⟩
  let v0 : CotangentSpace R := m.toCotangent x'
  have hx0 : v0 ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    simpa [pow_two] using hx2
  let L : Submodule (ResidueField R) (CotangentSpace R) := Submodule.span _ {v0}
  have hL : Module.finrank (ResidueField R) L = 1 := finrank_span_singleton hx0
  set q := Module.finrank (ResidueField R) (CotangentSpace R ⧸ L) with hq
  have hdim : q + 1 = Module.finrank (ResidueField R) (CotangentSpace R) := by
    rw [hq, ← hL, L.finrank_quotient_add_finrank]
  let bW := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ L)
  have hlift : ∀ i : Fin q, ∃ y : m, L.mkQ (m.toCotangent y) = bW i := by
    intro i
    obtain ⟨v, hv⟩ := L.mkQ_surjective (bW i)
    obtain ⟨y, rfl⟩ := m.toCotangent_surjective v
    exact ⟨y, hv⟩
  choose t ht using hlift
  let s : Set m := insert x' (Set.range t)
  have hspan : Submodule.span (ResidueField R) (m.toCotangent '' s) = ⊤ := by
    set S := Submodule.span (ResidueField R) (m.toCotangent '' s)
    have hLS : L ≤ S := Submodule.span_le.mpr (by
      rintro _ rfl
      exact Submodule.subset_span ⟨x', Set.mem_insert _ _, rfl⟩)
    have hmap : S.map L.mkQ = ⊤ := by
      rw [eq_top_iff, ← bW.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨m.toCotangent (t i), Submodule.subset_span ⟨t i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩,
        ht i⟩
    rw [Submodule.map_mkQ_eq_top] at hmap
    rwa [sup_eq_right.mpr hLS] at hmap
  have hspanR : Submodule.span R s = ⊤ := CotangentSpace.span_image_eq_top_iff.mp hspan
  have hmspan : m = Ideal.span (Subtype.val '' s) := by
    have := Submodule.map_span m.subtype s
    rw [hspanR, Submodule.map_subtype_top] at this
    exact this
  have hmax : maximalIdeal (R ⧸ span {x}) =
      Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) := by
    rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← hm,
      congrArg (Ideal.map (Ideal.Quotient.mk (span {x}))) hmspan, Ideal.map_span]
    have : (Ideal.Quotient.mk (span {x})) '' (Subtype.val '' s) =
        insert 0 (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) := by
      simp only [s, Set.image_insert_eq, ← Set.range_comp]
      congr 1
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
    rw [this, Ideal.span_insert_zero]
  have hle : (maximalIdeal (R ⧸ span {x})).spanFinrank ≤ q := by
    rw [hmax]
    have hfin : (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) =
        ((Finset.univ.image (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R)) :
          Finset (R ⧸ span {x})) : Set (R ⧸ span {x})) := by simp
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [hfin, Set.ncard_coe_finset]
    exact (Finset.card_image_le).trans (by simp)
  have hmr : m.spanFinrank = q + 1 := by
    rw [hm, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)]
    exact hdim.symm
  omega

private lemma exists_nat_of_le_add_one {d : WithBot ℕ∞} {n b : ℕ} (h2 : (n : WithBot ℕ∞) ≤ d + 1)
    (h3 : d ≤ b) : ∃ k : ℕ, d = k := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h2
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h4 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((b : ℕ∞) : WithBot ℕ∞) := h3
      rw [WithBot.coe_le_coe, top_le_iff] at h4
      exact ENat.natCast_ne_top b h4
    | coe k => exact ⟨k, rfl⟩

theorem isRegularLocalRing_quotient [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] :
    IsRegularLocalRing (R ⧸ span {x}) ∧ ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h1 := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    ((isRegularLocalRing_iff R).mp inferInstance).symm
  have h2 : ringKrullDim R ≤ ringKrullDim (R ⧸ span {x}) + 1 := by
    refine (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (span {x}) ?_).trans ?_
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact (span_singleton_le_iff_mem _).mpr hx
    · gcongr
      exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)).trans
        (by simp)
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal (R := R ⧸ span {x})
  rw [hR] at h2
  obtain ⟨k, hk⟩ := exists_nat_of_le_add_one h2 h3
  rw [hk] at h2 h3 ⊢
  have h2' : (maximalIdeal R).spanFinrank ≤ k + 1 := by exact_mod_cast h2
  have h3' : k ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank := by exact_mod_cast h3
  have hk' : (maximalIdeal (R ⧸ span {x})).spanFinrank = k := by omega
  refine ⟨(isRegularLocalRing_iff _).mpr (by rw [hk, hk']), ?_⟩
  rw [hR]
  exact_mod_cast (by omega : k + 1 = (maximalIdeal R).spanFinrank)

theorem IsRegularLocalRing.isDomain [IsRegularLocalRing R] : IsDomain R := by
  suffices H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → IsDomain S from H _ R rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hn
  have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
  by_cases h0 : n = 0
  · have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp (hn.trans h0)
    let := ((isField_iff_maximalIdeal_eq).mpr hbot).toField
    infer_instance
  · have hdim : ringKrullDim S = (n : WithBot ℕ∞) := by
      rw [← hn]; exact ((isRegularLocalRing_iff S).mp inferInstance).symm
    have hjac : maximalIdeal S ≤ jacobson ⊥ :=
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have hmin : ∀ P ∈ minimalPrimes S, ¬ maximalIdeal S ≤ P := by
      intro P hP hle
      have hPm : P = maximalIdeal S :=
        le_antisymm (IsLocalRing.le_maximalIdeal hP.1.1.ne_top) hle
      have : (maximalIdeal S).height = 0 := by
        rw [Ideal.height_eq_zero_iff, ← hPm]; exact hP
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, this] at hdim
      exact h0 (by exact_mod_cast hdim.symm)
    have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
      intro hle
      have : maximalIdeal S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
        (by simpa [pow_two, smul_eq_mul] using hle) hjac
      exact h0 (by rw [← hn, this]; simp)
    classical
    have hfin := minimalPrimes.finite_of_isNoetherianRing S
    obtain ⟨x, hx, hxn⟩ : ∃ x ∈ maximalIdeal S,
        x ∉ ⋃ i ∈ (↑(insert (maximalIdeal S ^ 2) hfin.toFinset) : Set (Ideal S)), (i : Set S) := by
      by_contra! hcon
      obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime (f := id) (maximalIdeal S ^ 2)
        (maximalIdeal S ^ 2) (fun i hi h1 _ ↦ by
          rcases Finset.mem_insert.mp hi with h | h
          · exact absurd h h1
          · exact ((Set.Finite.mem_toFinset _).mp h).1.1)).mp hcon
      rcases Finset.mem_insert.mp hi with h | h
      · exact hsq (h ▸ hle)
      · exact hmin i ((Set.Finite.mem_toFinset _).mp h) hle
    simp only [Finset.coe_insert, Set.Finite.coe_toFinset, Set.mem_insert_iff,
      Set.iUnion_iUnion_eq_or_left, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hxn
    obtain ⟨hx2, hxP⟩ := hxn
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    obtain ⟨hreg, -⟩ := isRegularLocalRing_quotient hx hx2
    have hlt := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have := ih _ (by omega) (S ⧸ span {x}) rfl
    have hprime : (span {x} : Ideal S).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := span {x}) bot_le
    have hxP' : x ∉ P := hxP P hP
    have hPsmul : P ≤ maximalIdeal S • P := by
      intro y hy
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp (hPle hy)
      have hz : z ∈ P := (hP.1.1.mem_or_mem hy).resolve_right hxP'
      rw [mul_comm]
      exact Submodule.smul_mem_smul hx hz
    have hPbot : P = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      P.fg_of_isNoetherianRing hPsmul hjac
    have : (⊥ : Ideal S).IsPrime := hPbot ▸ hP.1.1
    exact IsDomain.of_bot_isPrime S

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology

universe u

class IsNormalScheme (X : Scheme.{u}) : Prop where
  isDomain_stalk : ∀ x : X, IsDomain (X.presheaf.stalk x)
  isIntegrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

def PrimeDivisor (X : Scheme.{u}) : Type u :=
  {x : X // ringKrullDim (X.presheaf.stalk x) = 1}

abbrev WeilDivisor (X : Scheme.{u}) : Type u := PrimeDivisor X →₀ ℤ

variable {X : Scheme.{u}}

namespace PrimeDivisor

def point (x : PrimeDivisor X) : X := x.1

lemma ringKrullDim_stalk (x : PrimeDivisor X) :
    ringKrullDim (X.presheaf.stalk x.point) = 1 := x.2

lemma coheight_point (x : PrimeDivisor X) : Order.coheight x.point = 1 := by
  have h := x.ringKrullDim_stalk
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

lemma point_injective : Function.Injective (point (X := X)) := fun _ _ h => Subtype.ext h

lemma maximalIdeal_ne_bot (x : PrimeDivisor X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x.point) ≠ ⊥ := by
  intro h
  have hf : IsField (X.presheaf.stalk x.point) :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h
  have := x.ringKrullDim_stalk
  rw [ringKrullDim_eq_zero_of_isField hf] at this
  exact zero_ne_one this

variable [IsIntegral X]

lemma dimensionLEOne_stalk (x : PrimeDivisor X) :
    Ring.DimensionLEOne (X.presheaf.stalk x.point) := by
  have hle : Ring.KrullDimLE 1 (X.presheaf.stalk x.point) := by
    rw [Ring.krullDimLE_iff, x.ringKrullDim_stalk]
    norm_num
  refine ⟨fun {p} hp hprime => ?_⟩
  rcases Ring.krullDimLE_one_iff.mp hle p hprime with h | h
  · rw [IsDomain.minimalPrimes_eq_singleton_bot] at h
    exact absurd h hp
  · exact h

variable [IsLocallyNoetherian X] [IsNormalScheme X]

lemma isDedekindDomain_stalk (x : PrimeDivisor X) :
    IsDedekindDomain (X.presheaf.stalk x.point) := by
  have := x.dimensionLEOne_stalk
  have := IsNormalScheme.isIntegrallyClosed_stalk (X := X) x.point
  exact (isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk x.point))).mpr
    ⟨inferInstance, inferInstance, inferInstance,
      fun {y} hy => IsIntegrallyClosed.isIntegral_iff.mp hy⟩

noncomputable def heightOneSpectrum (x : PrimeDivisor X) :
    HeightOneSpectrum (X.presheaf.stalk x.point) :=
  ⟨IsLocalRing.maximalIdeal _, (IsLocalRing.maximalIdeal.isMaximal _).isPrime,
    x.maximalIdeal_ne_bot⟩

noncomputable def valuation (x : PrimeDivisor X) : Valuation X.functionField (WithZero (Multiplicative ℤ)) :=
  @HeightOneSpectrum.valuation _ _ x.isDedekindDomain_stalk _ _ _ _ x.heightOneSpectrum

noncomputable def ord (x : PrimeDivisor X) (f : X.functionField) : ℤ :=
  - WithZero.log (x.valuation f)

lemma ord_mul (x : PrimeDivisor X) {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    x.ord (f * g) = x.ord f + x.ord g := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hf) ((Valuation.ne_zero_iff _).mpr hg)]
  ring

end PrimeDivisor

namespace PrimeDivisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

lemma ord_algebraMap_of_isUnit (x : PrimeDivisor X) {a : X.presheaf.stalk x.point}
    (ha : IsUnit a) : x.ord (algebraMap _ X.functionField a) = 0 := by
  have := x.isDedekindDomain_stalk
  have h1 : x.valuation (algebraMap _ X.functionField a) = 1 := by
    simp only [valuation]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun hm => (IsLocalRing.mem_maximalIdeal a).mp hm ha
  simp [ord, h1]

lemma ord_germToFunctionField_of_isUnit (x : PrimeDivisor X) {U : X.Opens} [Nonempty U]
    (hx : x.point ∈ U) {g : Γ(X, U)} (hg : IsUnit g) :
    x.ord (X.germToFunctionField U g) = 0 := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
  exact x.ord_algebraMap_of_isUnit (hg.map _)

end PrimeDivisor

lemma PrimeDivisor.eq_genericPoint_of_mem [IsIntegral X] (x : PrimeDivisor X) {T : Set X}
    (hT : IsIrreducible T) (hTc : IsClosed T) (hgen : genericPoint X ∉ T) (hx : x.point ∈ T) :
    x.point = hT.genericPoint := by
  set c := hT.genericPoint
  have hc : IsGenericPoint c T := by
    have := hT.isGenericPoint_genericPoint_closure
    rwa [hTc.closure_eq] at this
  have hcx : c ⤳ x.point := hc.specializes hx
  have hcT : c ∈ T := hc.mem
  have hηc : genericPoint X ⤳ c := (genericPoint_spec X).specializes (Set.mem_univ _)
  have hηne : genericPoint X ≠ c := fun h => hgen (h ▸ hcT)
  have hlt1 : c < genericPoint X := by
    refine ⟨hηc, fun h => hηne (h.antisymm hηc).eq.symm⟩
  by_contra hne
  have hlt2 : x.point < c := ⟨hcx, fun h => hne (hcx.antisymm h).eq.symm⟩
  have h1 := Order.coheight_add_one_le hlt1
  have h2 := Order.coheight_add_one_le hlt2
  rw [x.coheight_point] at h2
  have h4 : (1 : ℕ∞) ≤ Order.coheight c := le_trans le_add_self h1
  have h5 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add_left h4 1) h2
  norm_num at h5

section Finite

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

theorem PrimeDivisor.finite_ord_ne_zero {f : X.functionField} (hf : f ≠ 0) :
    {x : PrimeDivisor X | x.ord f ≠ 0}.Finite := by
  obtain ⟨U, -, g, hne, hgf, hgu⟩ := exists_isUnit_germ_eq X f hf
  set Z : Set X := (U : Set X)ᶜ with hZ
  have hZc : IsClosed Z := U.isOpen.isClosed_compl
  have hgenU : genericPoint X ∈ U := by
    obtain ⟨⟨y, hy⟩⟩ := hne
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩
  have hsub : {x : PrimeDivisor X | x.ord f ≠ 0} ⊆ {x | x.point ∈ Z} := by
    intro x hx
    by_contra hxU
    simp only [Set.mem_ofPred_eq, hZ, Set.mem_compl_iff, not_not] at hxU
    exact hx (hgf ▸ x.ord_germToFunctionField_of_isUnit hxU hgu)
  refine Set.Finite.subset ?_ hsub
  have key : ∀ (x : PrimeDivisor X) (hx : x.point ∈ Z) (C : Set Z),
      C ∈ irreducibleComponents Z → (⟨x.point, hx⟩ : Z) ∈ C →
      ∃ hT : IsIrreducible (closure (Subtype.val '' C)), x.point = hT.genericPoint := by
    intro x hx C hC hxC
    have hT : IsIrreducible (closure (Subtype.val '' C)) :=
      (hC.1.image _ continuous_subtype_val.continuousOn).closure
    refine ⟨hT, x.eq_genericPoint_of_mem hT isClosed_closure ?_ ?_⟩
    · intro hg
      have : closure (Subtype.val '' C) ⊆ Z :=
        closure_minimal (Subtype.coe_image_subset _ _) hZc
      exact this hg hgenU
    · exact subset_closure ⟨_, hxC, rfl⟩
  have hcomp : ∀ x : {x : PrimeDivisor X | x.point ∈ Z}, ∃ C ∈ irreducibleComponents Z,
      {(⟨x.1.point, x.2⟩ : Z)} ⊆ C := fun x =>
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ isIrreducible_singleton
  let φ : {x : PrimeDivisor X | x.point ∈ Z} → irreducibleComponents Z := fun x =>
    ⟨(hcomp x).choose, (hcomp x).choose_spec.1⟩
  have : Finite (irreducibleComponents Z) :=
    (NoetherianSpace.finite_irreducibleComponents (α := Z)).to_subtype
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hx := (hcomp x).choose_spec
    have hy := (hcomp y).choose_spec
    have hC : (hcomp x).choose = (hcomp y).choose := congrArg Subtype.val hxy
    obtain ⟨hT, hxT⟩ := key x.1 x.2 _ hx.1 (hx.2 rfl)
    obtain ⟨hT', hyT⟩ := key y.1 y.2 _ hy.1 (hy.2 rfl)
    apply Subtype.ext
    apply PrimeDivisor.point_injective
    rw [hxT, hyT]
    simp only [hC]
  have : Finite {x : PrimeDivisor X | x.point ∈ Z} := Finite.of_injective φ hφ
  exact Set.toFinite _

end Finite

section Divisor

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]



end Divisor

end GroundTheory.Arith.SchemeCoh
end

