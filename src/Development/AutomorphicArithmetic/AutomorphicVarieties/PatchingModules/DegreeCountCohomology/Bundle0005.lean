module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GwBare
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LocBare

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPres
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

private theorem l_not_mem_base_prime (s : HidaSetting l L Ω) : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have h1 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← s.norm_v0_eq_one]
    simpa only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] using
      Ideal.absNorm_mem s.v0.asIdeal
  have hc : IsCoprime (s.p : 𝓞 (Lp L)) (l : 𝓞 (Lp L)) :=
    ((Nat.coprime_primes s.p_prime Fact.out).2 s.p_ne).cast
  obtain ⟨a, b, hab⟩ := hc
  exact s.v0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h)))

private def plF (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) : Vl l L ⊕ s.St ⊕ Option (Fin q) → Plc (Lp L)
  | .inl u => u.1
  | .inr (.inl u) => u.1
  | .inr (.inr none) => s.v0
  | .inr (.inr (some j)) => v j

private theorem plF_l (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) (hn : ∀ j, v j ∉ s.S) (w) :
    ((l : ℕ) : 𝓞 (Lp L)) ∈ (plF s v w).asIdeal ↔ ∃ u, w = .inl u := by
  rcases w with u | u | _ | j
  · exact iff_of_true u.2 ⟨u, rfl⟩
  · exact iff_of_false (s.St_l u.1 u.2) (by simp)
  · exact iff_of_false (l_not_mem_base_prime s) (by simp)
  · exact iff_of_false (fun h => hn j (Or.inl h)) (by simp)

private theorem plF_inj (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) (hi : Function.Injective v)
    (hn : ∀ j, v j ∉ s.S) : Function.Injective (plF s v) := by
  have key : ∀ (u : Vl l L) w, plF s v (.inl u) = plF s v (.inr w) → False := fun u w h => by
    have := (plF_l s v hn (.inr w)).1 (h ▸ u.2)
    simp at this
  rintro (a | a) (b | b) h
  · exact congrArg _ (Subtype.ext h)
  · exact (key _ _ h).elim
  · exact (key _ _ h.symm).elim
  · rcases a with a | _ | a <;> rcases b with b | _ | b <;> simp only [plF] at h
    · rw [Subtype.ext h]
    · exact (s.v0_St (h ▸ a.2)).elim
    · exact (hn b (h ▸ Or.inr (Or.inl a.2))).elim
    · exact (s.v0_St (h ▸ b.2)).elim
    · rfl
    · exact (hn b (Or.inr (Or.inr h.symm))).elim
    · exact (hn a (h ▸ Or.inr (Or.inl b.2))).elim
    · exact (hn a (Or.inr (Or.inr h))).elim
    · rw [hi h]

private theorem plF_range (s : HidaSetting l L Ω) {q : ℕ} (v : Fin q → Plc (Lp L)) :
    Set.range (plF s v) = s.S ∪ Set.range v := by
  ext x
  constructor
  · rintro ⟨u | u | _ | j, rfl⟩
    · exact Or.inl (Or.inl u.2)
    · exact Or.inl (Or.inr (Or.inl u.2))
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr ⟨j, rfl⟩
  · rintro ((h | h | h) | ⟨j, h⟩)
    · exact ⟨.inl ⟨x, h⟩, rfl⟩
    · exact ⟨.inr (.inl ⟨x, h⟩), rfl⟩
    · exact ⟨.inr (.inr none), h.symm⟩
    · exact ⟨.inr (.inr (some j)), h⟩

private def vaF (s : HidaSetting l L Ω) {q : ℕ} (B : Fin q → ValuationSubring Ω) :
    Vl l L ⊕ s.St ⊕ Option (Fin q) → ValuationSubring Ω
  | .inl u => s.A u.1
  | .inr (.inl u) => s.A u.1
  | .inr (.inr o) => o.elim (s.A s.v0) B

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.arPres :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (T : TWGrp (globOf r V0)) (_ : TWPl r T), V0.S' = s.S → ∀ N, ∃ (a : ArData (T.GN N) T.q (Module.finrank ℚ (Lp L))) (_ : ArPres a (Lp L) Ω), (∀ v : Vl l L, a.dv v = locDeg v.1) ∧ (((T.h N).p₀).comp (a.φq none)).range = V0.frame.D0 ∧ ∀ j, T.ph N j ∈ (a.φq (some j)).range ∧ T.ta N j ∈ (a.φq (some j)).range := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T P _ N
  classical
  obtain ⟨hex, hcc⟩ := ccEx l L Ω
  choose c hc using hex
  have hc' : ∀ w, ∃ j : Ω →+* ℂ, ∀ x, j (c w x) = starRingEnd ℂ (j x) := fun w => by
    obtain ⟨j, h, -⟩ := hc w
    exact ⟨j, h⟩
  have hcard : Fintype.card (InfinitePlace (Lp L)) = Module.finrank ℚ (Lp L) := by
    rw [IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  let ip : Fin (Module.finrank ℚ (Lp L)) ≃ InfinitePlace (Lp L) := (Fintype.equivFinOfCardEq hcard).symm
  have hε : ∀ g, (T.GN N).ε ((P.e N).p (toGS Ω (P.V N).S' g)) = cycZ (Lp L) Ω l g := fun g =>
    ((P.e N).ε _).trans (DFunLike.congr_fun (P.V N).hε g)
  let a : ArData (T.GN N) T.q (Module.finrank ℚ (Lp L)) :=
    { Dq := fun o => Dec (F := L) (vaF s (P.B N) (.inr (.inr o)))
      cpt := fun o => isCompact_iff_compactSpace.1 (isClosed_Dec (F := L) _).isCompact
      φq := fun o => (P.e N).p₀.comp ((P.V N).pr.comp (Dec (F := L) _).subtype)
      φq_cont := fun o => ((P.e N).cont.comp
        (((continuous_toGS Ω _).comp continuous_resP).comp continuous_subtype_val)).subtype_mk _
      cw := fun i => (P.e N).p (toGS Ω (P.V N).S' (c (ip i)))
      cw_sq := fun i => (map_mul (P.e N).p _ _).symm.trans
        ((congrArg (P.e N).p ((map_mul (toGS Ω (P.V N).S') _ _).symm.trans
          (by rw [(hcc _ (hc' _)).1, map_one]; rfl))).trans (map_one (P.e N).p))
      cw_η := fun i => ((P.e N).η _).trans
        ((Int.units_eq_one_or _).resolve_left fun h => (hcc _ (hc' _)).2.1 (((P.V N).hη _).1 h))
      cw_ε := fun i => (hε _).trans (hcc _ (hc' _)).2.2
      c_ε := by
        rw [← (P.e N).c]
        exact (hε s.c).trans (hcc _ s.hc).2.2
      dv := fun v => locDeg (Subtype.val v)
      sum_dv := by
        rw [← finsum_eq_sum_of_fintype]
        exact sumDegF l (Lp L) }
  have hsp : ∀ w, Dec (F := Lp L) (vaF s (P.B N) w) ≤ (resP L Ω).range := by
    rintro (u | u | _ | j)
    · exact s.split _ (Or.inl u.2)
    · exact s.split _ (Or.inr (Or.inl u.2))
    · exact s.split _ (Or.inr (Or.inr rfl))
    · exact P.split N j
  choose α hα using fun w => decSplit L Ω _ (hsp w)
  let e0 := MulEquiv.ofBijective (P.e N).p ⟨P.e_inj N, (P.e N).surj⟩
  have ec : Continuous e0.toEquiv := (P.e N).cont
  let e : GS Ω (P.V N).S' ≃ₜ* (T.GN N).Γ :=
    { e0 with
      continuous_toFun := (P.e N).cont
      continuous_invFun := (Continuous.homeoOfEquivCompactToT2 ec).symm.continuous }
  let pl : ArData.W (locOf r) T.q ≃ (P.V N).S' :=
    (Equiv.ofInjective _ (plF_inj s (P.v N) (P.v_inj N) (P.v_not N))).trans
      (Set.equivOfEq ((plF_range s _).trans (P.S_eq N).symm))
  refine ⟨a,
    { S := (P.V N).S'
      above := fun v hv => (P.V N).sub (Or.inl hv)
      e := e
      e_ε := hε
      pl := pl
      pl_l := fun w => plF_l s (P.v N) (P.v_not N) w
      A := vaF s (P.B N)
      isOver := ?_
      α := fun w => match w with
        | .inl u => α (.inl u)
        | .inr (.inl u) => α (.inr (.inl u))
        | .inr (.inr o) => α (.inr (.inr o))
      ι_eq := ?_
      dv_eq := fun v => rfl
      ip := ip
      c := fun i => c (ip i)
      cc := fun i => hc _
      cw_eq := fun i => rfl }, fun v => rfl, ?_, fun j => ⟨⟨⟨P.fr N j, P.fr_dec N j⟩, (P.ph N j).symm⟩, ?_⟩⟩
  · rintro (u | u | _ | j)
    · exact s.hA _
    · exact s.hA _
    · exact s.hA _
    · exact P.B_v N j
  · rintro (u | u | o) g
    · exact ((P.e N).φ u g).symm.trans (congrArg (fun x => (P.e N).p (toGS Ω _ x)) (hα (.inl u) g).symm)
    · exact ((P.e N).φu u g).symm.trans (congrArg (fun x => (P.e N).p (toGS Ω _ x)) (hα (.inr (.inl u)) g).symm)
    · exact congrArg (fun x => (P.e N).p (toGS Ω _ x)) (hα (.inr (.inr o)) g).symm
  · have : ((T.h N).p₀).comp (a.φq none) = V0.pr.comp (Dec (F := L) (s.A s.v0)).subtype :=
      MonoidHom.ext fun g => Subtype.ext (P.e_h N _)
    rw [this]
    exact (MonoidHom.range_comp _ _).trans (congrArg (Subgroup.map V0.pr) (Subgroup.range_subtype _))
  · exact ⟨⟨P.τ N j, Ine_le_Dec _ (P.τ_gen N j).1⟩, (P.ta N j).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AuxiliaryVectorCutByHermitianLinearForm
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem linearMap_comp_eq_on_smul_of_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (φ : ℤ_[l] →+* R)
    (h : ∀ y : R, l • y = 0) (τ : R →+ ZMod l) (a : ℤ_[l]) (y : R) :
    τ (φ a * y) = PadicInt.toZMod a * τ y := by
  have hspec := PadicInt.toZMod_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hspec
  obtain ⟨c, hc⟩ := hspec
  have ha : a = c * (l : ℤ_[l]) + ((PadicInt.toZMod a).val : ℤ_[l]) := by
    rw [hc, ZMod.cast_eq_val]
    ring
  have key : φ a * y = ((PadicInt.toZMod a).val : R) * y := by
    have e : φ a = φ c * (l : R) + ((PadicInt.toZMod a).val : R) := by
      rw [← map_natCast φ l, ← map_natCast φ, ← map_mul, ← map_add (f := _), ← ha]
    rw [e, add_mul, mul_assoc, ← nsmul_eq_mul l y, h y, mul_zero, zero_add]
  rw [key, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

private theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (m : ℕ) :
    ∃ τ : (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ m}) →+ ZMod l,
      ∀ y, (∀ z, τ (y * z) = 0) → y = 0 := by
  cases m with
  | zero =>
    refine ⟨0, fun y _ => ?_⟩
    have htop : Ideal.span {(PowerSeries.X : PowerSeries k) ^ 0} = ⊤ := by
      rw [pow_zero, Ideal.span_singleton_one]
    exact (Ideal.Quotient.subsingleton_iff.2 htop).elim _ _
  | succ k0 =>
    letI := ZMod.algebra k l
    obtain ⟨lam, -, hlam, -⟩ := UpperTheory.V.AlgebraTools.frob_form_trunc (k := k) l k0
    exact ⟨lam, hlam⟩

theorem UpperTheory.V.Pa.pair1 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m : ℕ), ∃ τ : x.Am m →+ ZMod l, (∀ y, (∀ z, τ (y * z) = 0) → y = 0) ∧ ∀ (a : ℤ_[l]) y, τ (algebraMap x.A (x.Am m) (algebraMap ℤ_[l] x.A a) * y) = PadicInt.toZMod a * τ y := by
  intro l _ F n x m
  obtain ⟨-, -, -, h4, -, -, -, -, hc⟩ := finAm l F n x m 0
  obtain ⟨τ, hτ⟩ := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero l x.K m
  exact ⟨τ, hτ, fun a y =>
    linearMap_comp_eq_on_smul_of_eq l (x.Am m) ((algebraMap x.A (x.Am m)).comp (algebraMap ℤ_[l] x.A)) h4 τ a y⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GaloisLiftMemFirstOrderDeformations
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Gen

variable {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ}

private theorem mem_blkMat_iff_mem_of_same_block_and_mem_off {V₁ V₂ : Submodule A R} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ blkMat n a V₁ V₂ ↔ ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ V₁) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ V₂) :=
  Iff.rfl

private theorem blk_tr {V₁ V₂ : Submodule A R} {Z : Matrix (Fin n) (Fin n) R} (hZ : Z ∈ blkMat n a V₁ V₂) :
    Zᵀ ∈ blkMat n a V₁ V₂ := by
  rw [mem_blkMat_iff_mem_of_same_block_and_mem_off] at hZ ⊢
  intro i j
  obtain ⟨h1, h2⟩ := hZ j i
  exact ⟨fun h => h1 h.symm, fun h => h2 (fun h' => h h'.symm)⟩

private def Act (U₁ U₂ V₁ V₂ : Submodule A R) : Prop :=
  (∀ u ∈ U₁, ∀ v ∈ V₁, u * v ∈ V₁) ∧ (∀ u ∈ U₁, ∀ v ∈ V₂, u * v ∈ V₂) ∧
    (∀ u ∈ U₂, ∀ v ∈ V₁, u * v ∈ V₂) ∧ (∀ u ∈ U₂, ∀ v ∈ V₂, u * v ∈ V₁)

private theorem blk_mul {U₁ U₂ V₁ V₂ : Submodule A R} (H : Act U₁ U₂ V₁ V₂) {P Z : Matrix (Fin n) (Fin n) R}
    (hP : P ∈ blkMat n a U₁ U₂) (hZ : Z ∈ blkMat n a V₁ V₂) : P * Z ∈ blkMat n a V₁ V₂ := by
  rw [mem_blkMat_iff_mem_of_same_block_and_mem_off] at hP hZ ⊢
  obtain ⟨h11, h12, h21, h22⟩ := H
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · exact h11 _ ((hP i k).1 hik) _ ((hZ k j).1 (hik.symm.trans hij))
    · have hkj : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun h => hik (hij.trans h.symm)
      exact h22 _ ((hP i k).2 hik) _ ((hZ k j).2 hkj)
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hkj : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun h => hij (hik.trans h)
      exact h12 _ ((hP i k).1 hik) _ ((hZ k j).2 hkj)
    · have hkj : ((k : ℕ) < a ↔ (j : ℕ) < a) := by tauto
      exact h21 _ ((hP i k).2 hik) _ ((hZ k j).1 hkj)

private theorem blk_sand {U₁ U₂ V₁ V₂ : Submodule A R} (H : Act U₁ U₂ V₁ V₂) {P Q Z : Matrix (Fin n) (Fin n) R}
    (hP : P ∈ blkMat n a U₁ U₂) (hQ : Q ∈ blkMat n a U₁ U₂) (hZ : Z ∈ blkMat n a V₁ V₂) :
    P * Z * Q ∈ blkMat n a V₁ V₂ := by
  have h1 := blk_mul H hP hZ
  have h2 := blk_tr (blk_mul H (blk_tr hQ) (blk_tr h1))
  simpa [Matrix.transpose_mul] using h2

private theorem alg_smul_mem {V : Submodule A (Matrix (Fin n) (Fin n) R)} (c : A) {Z : Matrix (Fin n) (Fin n) R}
    (hZ : Z ∈ V) : algebraMap A R c • Z ∈ V := by
  rw [algebraMap_smul]
  exact V.smul_mem c hZ

end Gen

section Parts

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ}

private theorem ep_algebraMap_eq_zero (c : A) (j : Fin g) : (algebraMap A (DD X g) c).ep j = 0 := rfl

private theorem ep'_algebraMap_eq_zero (c : A) (j : Fin g) : (algebraMap A (DD X g) c).ep' j = 0 := rfl

private theorem eta_algebraMap_eq_zero (c : A) : (algebraMap A (DD X g) c).eta = 0 := rfl

private theorem mem_part {p q r s : Bool} {y : DD X g} : y ∈ ddPart A X g p q r s ↔
    (p = false → y.a = 0) ∧ (q = false → ∀ j, y.ep j = 0) ∧ (r = false → ∀ j, y.ep' j = 0) ∧ (s = false → y.eta = 0) := by
  show ((p = false → y.a = 0) ∧ (q = false → y.ep = 0) ∧ (r = false → y.ep' = 0) ∧ (s = false → y.eta = 0)) ↔ _
  simp only [funext_iff, Pi.zero_apply]

private theorem act1 : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g true false false false) (ddPart A X g false true false false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

private theorem act1s : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g false false false true) (ddPart A X g false false true false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

private theorem act2 : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g false false true false) (ddPart A X g false false false true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

end Parts

private theorem galois_lift_mem_first_order_deformations {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (g : F.G₀) : k.ρ1 X g ∈ W1 n x.A X k.g x.a := by
  have hP : (1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) ∈ W1 n x.A X k.g x.a := by
    show _ ∈ blkMat n x.a (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false)
    refine mem_blkMat_iff_mem_of_same_block_and_mem_off.2 (fun i j => ⟨fun h => ?_, fun h => ?_⟩)
    · have hκ : ∀ m, k.κ m g i j = 0 := fun m => by
        have hm := ((mem_blkMat_iff_mem_of_same_block_and_mem_off.1 ((k.mem m).1 g)) i j).1 h
        simpa using hm
      rw [mem_part]
      by_cases hij : i = j
      · subst hij
        simp [Matrix.one_apply, DD.epM, hκ]
      · simp [hij, Matrix.one_apply, DD.epM, hκ]
    · have hne : i ≠ j := by
        rintro rfl
        exact h Iff.rfl
      rw [mem_part]
      simp [hne, Matrix.one_apply, DD.epM]
  have hZ : x.ρX (DD X k.g) g ∈ W1 n x.A X k.g x.a := by
    show _ ∈ blkMat n x.a (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false)
    refine mem_blkMat_iff_mem_of_same_block_and_mem_off.2 (fun i j => ⟨fun h => ?_, fun h => ?_⟩)
    · rw [mem_part]
      simp [NP.ρX, ep_algebraMap_eq_zero, ep'_algebraMap_eq_zero, eta_algebraMap_eq_zero]
    · have h0 : (mat x.ρ) g i j = 0 := by
        simpa using ((mem_blkMat_iff_mem_of_same_block_and_mem_off.1 (x.blk g)) i j).2 h
      rw [mem_part]
      simp [NP.ρX, h0]
  exact blk_mul act1 hP hZ

theorem UpperTheory.V.Pa.ok1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X] (χ : G.Γ →* x.A), AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (W1 n x.A X k.g x.a) ∧ AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a) ∧ AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (W2 n x.A X k.g x.a) := by
  intro l _ L G G0 h n x k X _ _ χ
  obtain ⟨r1, r2, r3, -, -⟩ := rho1 l G0.frame n x k X
  have hconj : ∀ g : G.frame.G₀, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
    intro g
    apply Subtype.ext
    simp [Glob.Hom.p₀, GFrame.conj, h.c]
  have key : ∀ V₁ V₂ : Submodule x.A (DD X k.g),
      Act (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false) V₁ V₂ →
      AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (blkMat n x.a V₁ V₂) := by
    intro V₁ V₂ H
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show k.ρ1 X (h.p₀ 1) = 1
      rw [map_one]
      exact r1
    · intro a b
      show k.ρ1 X (h.p₀ (a * b)) = k.ρ1 X (h.p₀ a) * k.ρ1 X (h.p₀ b)
      rw [map_mul]
      exact r2 _ _
    · intro g
      refine ⟨Units.map (algebraMap x.A (DD X k.g) : x.A →* DD X k.g)
        ((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))), ?_⟩
      show (k.ρ1 X (h.p₀ g))ᵀ * k.ρ1 X (h.p₀ (G.frame.conj g)) = _
      rw [hconj, r3]
      rfl
    · show algebraMap x.A (DD X k.g) (χ 1) = 1
      simp
    · intro a b
      show algebraMap x.A (DD X k.g) (χ (a * b)) = algebraMap x.A (DD X k.g) (χ a) * algebraMap x.A (DD X k.g) (χ b)
      simp
    · intro g Z hZ
      show algebraMap x.A (DD X k.g) (χ g) • (k.ρ1 X (h.p₀ g) * Z * k.ρ1 X (h.p₀ g⁻¹)) ∈ _
      exact alg_smul_mem _ (blk_sand H (galois_lift_mem_first_order_deformations k X _) (galois_lift_mem_first_order_deformations k X _) hZ)
    · intro Z hZ
      show algebraMap x.A (DD X k.g) (χ G.frame.c) • Zᵀ ∈ _
      exact alg_smul_mem _ (blk_tr hZ)
  exact ⟨key _ _ act1, key _ _ act1s, key _ _ act2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PresCounts
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.presCounts :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (Lc : Loc) (G : Glob l Lc) (q d : ℕ) (a : ArData G q d) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (_ : ArPres a F Ω), l ≠ 2 → (∀ u, UnrCount l (Lc.Gu u) (Lc.Ju u)) → a.Counts := by
  intro hC l _ Lc G q d a F Ω _ _ _ _ _ _ P hl hU
  obtain ⟨hLF, hLTD, hLEC, hGF, _, hGW, _, _⟩ := hC
  have key : ∀ (w : ArData.W Lc q) (n : ℕ),
      LocCount (↥(Dec (P.A w))) ((cycZ F Ω l).comp (Dec (P.A w)).subtype) n →
        LocCount (a.D w) (G.ε.comp (a.ι w)) n := by
    intro w n hn
    refine locCongr l (a.D w) (↥(Dec (P.A w))) (P.α w) (G.ε.comp (a.ι w))
      ((cycZ F Ω l).comp (Dec (P.A w)).subtype) n ?_ hn
    intro g
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [P.ι_eq w g, P.e_ε]
  have notl : ∀ (w : ArData.W Lc q), (∀ v, w ≠ Sum.inl v) →
      LocCount (a.D w) (G.ε.comp (a.ι w)) 0 := by
    intro w hw
    apply key
    refine (locBare hLF hLTD hLEC l F Ω (P.A w) (↑(P.pl w)) (P.isOver w)).2 ?_
    rw [P.pl_l]
    rintro ⟨v, hv⟩
    exact hw v hv
  have hcw : a.cw = fun i => P.e ((toGS Ω P.S) (P.c i)) := funext P.cw_eq
  refine ⟨?_, ?_, ?_, ?_, hU⟩
  · rw [hcw]
    exact gwBare hGW hLTD hGF hLF l F Ω P.S G.Γ P.e G.ε (ArData.W Lc q) P.pl P.A a.D a.ι P.α d P.ip P.c
      hl P.above P.e_ε P.isOver P.ι_eq P.cc
  · intro v
    have h1 := (locBare hLF hLTD hLEC l F Ω (P.A (Sum.inl v)) (↑(P.pl (Sum.inl v))) (P.isOver _)).1
      ((P.pl_l _).2 ⟨v, rfl⟩)
    rw [← P.dv_eq v] at h1
    exact key (Sum.inl v) _ h1
  · intro u
    exact notl (Sum.inr (Sum.inl u)) (fun v h => by cases h)
  · intro j
    exact notl (Sum.inr (Sum.inr j)) (fun v h => by cases h)
end

