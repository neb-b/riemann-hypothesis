module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0066
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.ExistsSplittingAuxiliaryCharacterForTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedSym
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.SplitOfDecAlt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ConjEquivApply
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open UpperTheory.V.Af

namespace UpperTheory.V.Z.Win.Birth

section Conj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

private def conjEquiv (g : GL (Fin n) k) : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))
    (Matrix.mulVecLin ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (by rw [← Matrix.mulVecLin_mul, ← Units.val_mul, mul_inv_cancel]; simp)
    (by rw [← Matrix.mulVecLin_mul, ← Units.val_mul, inv_mul_cancel]; simp)

private theorem conjEquiv_apply (g : GL (Fin n) k) (v : Fin n → k) :
    conjEquiv g v = (g : Matrix (Fin n) (Fin n) k).mulVec v := rfl

private theorem intertwine {r r' : Γ →* GL (Fin n) k} {g : GL (Fin n) k}
    (hg : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) (v : Fin n → k) :
    (r' s : Matrix (Fin n) (Fin n) k).mulVec (conjEquiv g v) =
      conjEquiv g ((r s : Matrix (Fin n) (Fin n) k).mulVec v) := by
  have h : (r' s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) =
      (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k) := by
    rw [← Units.val_mul, ← Units.val_mul, hg s, inv_mul_cancel_right]
  simp only [conjEquiv_apply, Matrix.mulVec_mulVec, h]

private theorem ss_of_conj {r r' : Γ →* GL (Fin n) k} (h : RepIso r r') (H : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  intro W hW
  have h0 : IsInv r (W.comap (conjEquiv g).toLinearMap) := by
    intro s v hv
    have hv' : conjEquiv g v ∈ W := hv
    show conjEquiv g _ ∈ W
    rw [← intertwine hg]
    exact hW s _ hv'
  obtain ⟨W', hW', hc⟩ := H _ h0
  refine ⟨W'.map (conjEquiv g).toLinearMap, ?_, ?_⟩
  · rintro s _ ⟨v, hv, rfl⟩
    exact ⟨(r s : Matrix (Fin n) (Fin n) k).mulVec v, hW' s v hv, (intertwine hg s v).symm⟩
  · have hm := (Submodule.orderIsoMapComap (conjEquiv g)).isCompl hc
    have hW2 : (Submodule.orderIsoMapComap (conjEquiv g)) (W.comap (conjEquiv g).toLinearMap) = W := by
      ext x
      simp [Submodule.orderIsoMapComap_apply, Submodule.mem_map]
    rw [hW2] at hm
    exact hm

end Conj

private theorem frob_of_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : RepIso r r')
    {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂ} (H : FrobEig ι r w B) : FrobEig ι r' w B := by
  obtain ⟨g, hg⟩ := h
  intro A hA
  obtain ⟨h1, h2⟩ := H A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · rw [hg s, h1 s hs, mul_one, mul_inv_cancel]
  · rw [hg σ⁻¹, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact h2 σ hσ

theorem prIso : PrIso := by
  intro F Ω _ _ _ _ _ _ l _ ι n r r' h
  rintro ⟨π, h1, h2, h3⟩
  exact ⟨π, h1, ⟨ss_of_conj h h2.1, h2.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, frob_of_conj h hB'⟩⟩, h3⟩

end UpperTheory.V.Z.Win.Birth
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ContRes
section
open UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem cont_res {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω)
    [NumberField F] : Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

private theorem not_both {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (h : p.Coprime q)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := by
  intro hq
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * p + (b : Ω) * q = 1 := by exact_mod_cast congrArg (Int.cast (R := Ω)) hab
  have hz : ∀ (z : ℤ) (x : Ω), A.valuation x < 1 → A.valuation (z * x) < 1 := fun z x hx => by
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right ((A.valuation_le_one_iff _).2 (intCast_mem A z)) zero_le hx
  have := A.valuation.map_add_lt (hz a _ hp) (hz b _ hq)
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem UpperTheory.V.Z.Win.Birth.mixOfP :
    MixSeedP → MixOfP := by
  intro hP Ω _ _ _ l hl c D T k₀ _ _ φ ι H C
  have hl2 : l ≠ 2 := H.good.l_odd
  obtain ⟨hsp, w, w', hne, hw, hw', hpl⟩ := UpperTheory.quadratic_field_split_prime_two_places Ω k₀ H.deg l hl.out H.spl
  obtain ⟨hsp2, u, -, -, hu, -, -⟩ := UpperTheory.quadratic_field_split_prime_two_places Ω k₀ H.deg 2 Nat.prime_two H.sp2
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  have hker : ∀ g : G ℚ Ω, D.ξ g = 1 → up D.ξ g = 1 := fun g hg => by
    change Units.map _ (D.ξ g) = 1
    rw [hg, map_one]
  have lift : ∀ g : G T.F Ω, resQ T.F g ∈ k₀.fixingSubgroup → ∃ s : G k₀ Ω, resQ k₀ s = resQ T.F g := fun g hg =>
    ⟨k₀.fixingSubgroupEquiv ⟨_, hg⟩, rfl⟩
  obtain ⟨Au, hAu⟩ := exists_isPlaceOver Ω u
  have hAu2 : Au.valuation ((2 : ℕ) : Ω) < 1 := by
    have h := (hAu _).2 hu
    rwa [show algebraMap k₀ Ω (((2 : ℕ) : 𝓞 k₀) : k₀) = ((2 : ℕ) : Ω) from
      map_natCast ((algebraMap k₀ Ω).comp (algebraMap (𝓞 k₀) k₀)) 2] at h
  obtain ⟨g, hg, hg4⟩ := H.two.big2 Au (by simpa using hAu2)
  rw [Ne, C.al] at hg4
  obtain ⟨s, hs⟩ := lift g (H.sp2 Au hAu2 hg.1)
  have hsI : s ∈ Ine (F := k₀) Au := by
    have h1 : resQ T.F g ∈ Ine (F := ℚ) Au := ⟨hg.1, hg.2⟩
    rw [← hs] at h1
    exact ⟨h1.1, h1.2⟩
  obtain ⟨k, t, π, r, hk, ht, hkl, -, hc, hi, ha, hd, hr, ⟨haw, hrw⟩, hab⟩ :=
    hP k₀ Ω l hl2 (by rw [H.deg]; exact even_two) hsp ι ((up D.ξ).comp (resQ k₀))
      (Subgroup.isOpen_mono (H₁ := D.ξ.ker.comap (resQ k₀)) (fun x hx => hker _ hx)
        (H.good.xi_open.preimage (cont_res k₀)))
      (fun x hx => by
        have h1 : IsConj (resQ k₀ x) D.cc := UpperTheory.complex_conjugations_are_conjugate Ω _ _ hx H.good.isCC
        have h2 : D.ξ (resQ k₀ x) = -1 := by
          rw [← H.good.xi_odd]
          exact isConj_iff_eq.1 (D.ξ.map_isConj h1)
        change Units.map _ (D.ξ (resQ k₀ x)) = -1
        rw [h2]
        exact Units.ext (by simp))
      (fun A hA x hx => hker _ (H.two.xi A (fun p hp => by
        rw [Finset.mem_singleton.1 hp]
        exact not_both A ((Nat.coprime_primes hl.out Nat.prime_two).2 hl2) hA) ⟨hx.1, hx.2⟩))
      ⟨u, Au, (by
        rw [show normV u = Ideal.absNorm u.asIdeal by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
          rfl]
        exact (hsp2 u hu).1), hAu, fun h => hg4 (by
        have h1 : up D.ξ (resQ k₀ s) = 1 := h hsI
        rw [← hs, h1]
        simp [Cong])⟩
      ⟨s ^ 2, by
        rw [map_pow, ← pow_mul, MonoidHom.comp_apply, hs]
        exact hg4⟩
      (fun A hA => by
        obtain ⟨x, hx, hx4⟩ := H.two.bigL A hA
        rw [Ne, C.al] at hx4
        obtain ⟨y, hy⟩ := lift x (H.spl A hA hx)
        have h1 : resQ T.F x ∈ Dec (F := ℚ) A := hx
        rw [← hy] at h1
        refine ⟨y ^ 4, pow_mem (show y ∈ Dec (F := k₀) A from h1) 4, ?_⟩
        rw [map_pow, MonoidHom.comp_apply, hy]
        exact hx4)
      {w} ⟨w, rfl, hw⟩ ⟨w', hne.symm, hw'⟩
  obtain ⟨h1, h1'⟩ := (hab w hw).1 rfl
  obtain ⟨h2, h2'⟩ := (hab w' hw').2 hne.symm
  obtain ⟨he, he'⟩ := UpperTheory.exists_ringHom_to_localField_inducing_place k₀ l ι
  obtain ⟨τ, hτ⟩ := he w hw
  obtain ⟨τ', hτ'⟩ := he w' hw'
  refine ⟨k, t, r, And.symm ⟨hrw, ?_⟩⟩
  refine ⟨hk, ht, hkl, hc, hi, ⟨π, ha, _, _, fun h => hne (he' w w' τ τ' hτ hτ' h), h1' τ hτ, h2' τ' hτ'⟩,
    hd, hr, haw, fun A A' hA x hx hAA => ?_⟩
  rcases hpl A A' hA x hx hAA with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨h1 A a, h2 A' b⟩
  · exact Or.inr ⟨h2 A a, h1 A' b⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.FinOrdKills
section
open UpperTheory.V.Z.Win.Birth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

private theorem finOrd_kills {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] {M : ℕ} (hM : 1 ≤ M) {φ : G ℚ Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) : IsOfFinOrder φ := by
  have ho : IsOpen (φ.ker : Set (G ℚ Ω)) := by
    have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
      classical
      refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
      simpa [Polynomial.mem_nthRoots hM] using hζ
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
    · simp only [Set.mem_iInter]
      exact fun ζ _ => Subgroup.one_mem _
    · simp only [Set.mem_iInter] at hs
      exact hφ s fun ζ hζ => hs ζ hζ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfi : Finite (G ℚ Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨_, hpos, MonoidHom.ext fun s => ?_⟩
  rw [MonoidHom.pow_apply, ← map_pow]
  exact φ.ker.pow_index_mem s

private theorem cong_iff {l : ℕ} [Fact l.Prime] {c : Coef l} (a : c.Oˣ) :
    Cong (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom a) 1 ↔ residue c.O a = 1 := by
  rw [← map_one (residue c.O), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, (UpperTheory.V.Fr.sc_norm l c _).2]
  rfl

private theorem toB_chi {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    (g : G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl

theorem rhoExP (h1 : ExistsSplittingAuxiliaryCharacterForTower) (h2 : PhiFacts) (h3 : ModEx4) : RhoExP := by
  intro hP Ω _ _ _ l _ c D T₀ hctx hok hfour ι B c₀
  obtain ⟨N, w, θ, haux, hsp, hw⟩ := h1 Ω l c D T₀ hctx hfour
  obtain ⟨hcc, hev, hk⟩ := h2 Ω l c D T₀ hctx hok hfour
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two haux.odd
  have hcc' : toB (phi D T₀.pr) D.cc = -1 := by
    show Units.map _ (phi D T₀.pr D.cc) = _
    rw [hcc]
    ext
    simp
  have hne : toB (phi D T₀.pr) ≠ 1 := by
    intro h
    have h' := congrArg (fun u : (Qbar l)ˣ => (u : Qbar l)) hcc'
    rw [h] at h'
    simp only [MonoidHom.one_apply, Units.val_one, Units.val_neg] at h'
    have h2' : (2 : Qbar l) = 0 := by linear_combination h'
    exact two_ne_zero h2'
  have hfin : IsOfFinOrder (toB (phi D T₀.pr)) := finOrd_kills haux.pos hsp.1
  obtain ⟨k₀, hk₀⟩ := hP l Ω ι D.cc hctx.1.isCC N w (toB (phi D T₀.pr)) θ haux hsp hne
  obtain ⟨n, hn⟩ : ∃ n, n = B + k₀ + 2 := ⟨_, rfl⟩
  have hl1 : 1 ≤ l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have hle : n ≤ (l - 1) * n := Nat.le_mul_of_pos_left n hl1
  have hev' : Even ((l - 1) * n) := (Nat.Odd.sub_odd hodd odd_one).mul_right n
  obtain ⟨k, hkdef⟩ : ∃ k, k = D.e + 1 + (l - 1) * n := ⟨_, rfl⟩
  have hkodd : Odd k := by
    rw [hkdef, add_assoc, add_comm 1, ← add_assoc]
    exact (hev.add hev').add_one
  have hk1 : 1 ≤ k := by omega
  have hcong : k - 1 ≡ D.e [MOD l - 1] := by
    unfold Nat.ModEq
    rw [show k - 1 = D.e + (l - 1) * n by omega, Nat.add_mul_mod_self_left]
  obtain ⟨ρ, hρ, hrw⟩ := hk₀ k (by omega) (by rw [hcc', hkodd.neg_one_pow])
  obtain ⟨hsq, hdec⟩ := hk k hk1 hcong
  have e : ∀ g, (cycBar ℚ Ω l ^ (k - 1) * toB (phi D T₀.pr)) g =
      Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Phi D T₀.pr k g) := by
    intro g
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Phi, map_mul, map_pow]
    rw [← toB_chi c g]
    rfl
  have hI : IrrOpen ρ := by
    refine (sI l haux.odd Ω ι _ θ k (by omega) hfin ρ hρ).2 ⟨resQ T₀.F T₀.g0, fun h => hsq ?_⟩
    rw [e] at h
    have := (cong_iff (Phi D T₀.pr k (resQ T₀.F T₀.g0) ^ 2)).1 (by rw [map_pow]; exact h)
    rwa [Units.val_pow_eq_pow_val, map_pow] at this
  have hg1 : Raw.bar (Phi D T₀.pr k) (resQ T₀.F T₀.g0) ≠ 1 := fun h => hsq (by rw [h, one_pow])
  obtain ⟨c₁, h, ρ₁, x, hc₀, hM⟩ := h3 Ω l ι c D T₀.pr θ k hk1 ρ hρ hdec (resQ T₀.F T₀.g0) hg1 c₀
  exact ⟨w, θ, k, ρ, c₁, h, ρ₁, x, haux.prime, hw, haux.pow, haux.mu, by omega, hcong, hρ, ⟨hI, hrw⟩, hc₀, hM⟩

end UpperTheory.V.Cu2

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.GenericR
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic UpperTheory.V

namespace UpperTheory.V.Z.Win.Birth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem good_of_isCuspFormR (a : ℕ) (ψ : AddChar (Ad F) ℂ) (φ : TR.Sm F a) (h : TR.IsCuspForm φ) :
    Good ψ (a - 1) φ.1 := by
  have hcont : Continuous φ.1 := GlobalTheory.SlTwoCusp.continuous_of_isOpen_stab F a φ h.1.level
  refine ⟨hcont, fun γ _ g => h.1.left γ g, ?_, ?_⟩
  · intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex a k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast a k) (0 : UnipotentBlockColumnIndex a k k → Ad F) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hra g
    have hra' : r < a := by omega
    have hper := per_blk (E := F) (r := r) (m := a - 1) hcont (fun c g => h.1.left _ g) g
    have hper2 : Per (ratN F a r) (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) :=
      ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
        simp only [map_add (f := _)]
        exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
    have key := _root_.GlobalTheory.CuspGeneric.avg_equiv _ _ (ratN F a r) (ratV F _) (isCoLat_ratV F (BlockIx a r))
      (isCoLat_ratV F _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
    rw [← key]
    have hfun : (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) = fun x => φ.1 (unip x * g) :=
      funext fun x => by rw [← blkU_comp_equiv]; rfl
    rw [hfun] at hper2 ⊢
    letI : MeasurableSpace (BlockIx a r → Ad F) := borel _
    haveI : BorelSpace (BlockIx a r → Ad F) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := _root_.GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one _ (ratN F a r) (isCoLat_ratV F (BlockIx a r))
    obtain ⟨-, -, -, hint⟩ := _root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg _ _ (isCoLat_ratV F (BlockIx a r)) μ 𝓕 hμ hF _ hper2
    have hc := h.2 r hr hra' μ 𝓕 hμ hF g
    rw [hint, h1] at hc
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc
    exact hc

private theorem exists_split_locR (a : ℕ) (w : HeightOneSpectrum (𝓞 F)) (g : GA F a) :
    ∃ (h : GA F a) (gw : GL (Fin a) (w.adicCompletion F)),
      g = h * finGL F a (locGL F a w gw) ∧
        ∀ u : GL (Fin a) (w.adicCompletion F),
          h * finGL F a (locGL F a w u) = finGL F a (locGL F a w u) * h := by
  obtain ⟨gw, hgw⟩ : ∃ gw, gw = GeneralLinearGroup.map (pLoc F w) (GeneralLinearGroup.map (pFin F) g) := ⟨_, rfl⟩
  refine ⟨g * (finGL F a (locGL F a w gw))⁻¹, gw, by rw [inv_mul_cancel_right], fun u => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc F w)
      (GeneralLinearGroup.map (pFin F) (g * (finGL F a (locGL F a w gw))⁻¹)) = 1 := by
    rw [map_mul, map_inv, pFin_finGL, map_mul, map_inv, pLoc_locGL, hgw, mul_inv_cancel]
  generalize g * (finGL F a (locGL F a w gw))⁻¹ = k at hk ⊢
  obtain ⟨y, z, rfl, hz⟩ : ∃ y z, k = TR.infGL F a y * finGL F a z ∧ GeneralLinearGroup.map (pLoc F w) z = 1 :=
    ⟨_, _, (TR.infGL_mul_finGL k).symm, hk⟩
  rw [mul_assoc, ← map_mul, LocUniq.comm_locGL w hz u, map_mul, ← mul_assoc, TR.infGL_comm, mul_assoc]

private theorem locTri_adelicR (a : ℕ) (w : HeightOneSpectrum (𝓞 F)) (u : GL (Fin a) (w.adicCompletion F))
    (hlow : ∀ i j : Fin a, j < i → u.val i j = 0) (hdiag : ∀ j : Fin a, u.val j j = 1) :
    (∀ i j : Fin a, j < i → (finGL F a (locGL F a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL F a (locGL F a w u)).val j j = 1) ∧
      ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL F a (locGL F a w u)).val p.1 p.2 =
        sFin F (sLoc F w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  have hoff : ∀ i j : Fin a, i ≠ j → (finGL F a (locGL F a w u)).val i j = sFin F (sLoc F w (u.val i j)) := by
    intro i j h
    rw [finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    rw [hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]
  · intro j
    exact cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))
  set_option synthInstance.maxHeartbeats 100000 in
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ p.2 := by
      intro h; rw [h] at hp'; omega
    exact hoff p.1 p.2 hne


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem isGeneric_of_isLocCompR (a : ℕ) (P : TR.CuspSub F a) (w : HeightOneSpectrum (𝓞 F))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion F))) (hσ : P.IsLocComp w σ) : GlobalTheory.LocGL.IsGeneric σ.ρ := by
  obtain ⟨f, hf0, hf⟩ := hσ
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.CuspGeneric.exists_stdPsi F
  have hg : ∀ v, Good ψ (a - 1) (f v).1.1 := fun v => good_of_isCuspFormR a ψ (f v).1 (P.cusp _ (f v).2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  have hv1 : (f v₀).1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := exists_split_locR a w g₀
  have hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x =
      whit ψ (a - 1) (f v).1.1 (x * finGL F a (locGL F a w u)) := fun u v x => by
    rw [hf u v]
    exact whit_rt _ _ _ _
  let l : σ.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) (f v).1.1 h
      map_add' := fun v v' => by
        rw [map_add f]
        exact congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => by
        rw [map_smul f]
        exact congrFun (whit_smul (a - 1) c (f v).1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) (f v).1.1 h := fun _ => rfl
  have hne : l (σ.ρ gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion F) (Fin a)) v,
      l (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion F)).val p.1 p.2) : ℂ) * l v := by
    intro u v
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 u.2
    obtain ⟨t1, t2, t3⟩ := locTri_adelicR a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic F a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3]
    rfl
  refine ⟨locPsi hψ w, ?_, fun h1 => ?_, ?_⟩
  · refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af F => ((0, x) : InfiniteAdeleRing F × Af F)).comp
      (CuspSub.continuous_sLoc w)
  · obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  · refine Submodule.Quotient.nontrivial_iff.2 fun htop => hne ?_
    have hle : GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion F) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤
        LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw, smul_eq_mul]
      exact sub_eq_zero.2 rfl
    exact hle (htop ▸ Submodule.mem_top)

end UpperTheory.V.Z.Win.Birth
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PrOrd
section
theorem UpperTheory.V.Z.Win.Birth.prOrd :
    UpperTheory.V.Z.Win.Birth.PrOrd := by
  intro F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r h
  refine ⟨π, h.reg, h.att, fun v => ?_⟩
  by_cases hB : ∃ B, π.HasSat v B
  · exact Or.inr hB
  · exact Or.inl fun σ hσ =>
      (UpperTheory.V.Z.Win.Birth.ordPlain F Ω l ι ξ s c m a π r h v σ hσ).resolve_right hB
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ThruBad
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

namespace UpperTheory.V.Z.Win.Birth

def AllW {F Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ π : CuspSub F n, (CG.mk π).IsRegAlg → AttC ι r π → ImaginaryQuadraticEtaCharacter.AllWin π

theorem AllW.witA {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} (h : AllW ι r)
    (hp : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → PotUnl r v) : WitA ι r :=
  ⟨fun v hv _ => hp v hv, fun π h1 h2 => (h π h1 h2).imp fun _ ht v _ => ht v⟩

def AllC (p : ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ),
    (Qbar l ≃+* ℂ) → (G F Ω →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), 2 ≤ n →
    ∀ ι r, p F Ω l n ι r

def AwOne : Prop := AllC fun F _ _ _ _ _ _ _ _ n ι r => ∀ π : CuspSub F n, AttC ι r π → ImaginaryQuadraticEtaCharacter.AllWin π → AllW ι r

def AwTw : Prop := AllC fun F Ω _ _ _ _ _ l _ _ ι r => ∀ κ : G F Ω →* (Qbar l)ˣ, Sd.IsAlgChar ι κ → IsAutC ι r → AllW ι r → AllW ι (tw r κ)

def AwReal : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure F Ω], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin 2) (Qbar l)), Continuous r → IsIrr (r.comp (galEmb F E Ω)) → PR ι r → AllW ι (r.comp (galEmb F E Ω))

def AwUp : Prop :=
  UpCyc → ∀ (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 2 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutC ι r →
      IsIrr (r.comp (galEmb F E Ω)) → AllW ι r → AllW ι (r.comp (galEmb F E Ω))

def ThruBad : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ π : CuspSub M 2, Z.InvariantSubmoduleMonicPolynomial.E.SplitBad K π →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : GroundTheory.Global.SemiLocal.PlacesOver M v), Z.Gam.ThruAt π w

def AwInd : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field Ω]
    [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure M Ω], Module.finrank K M = 2 →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : CuspSub M 2) (r : G M Ω →* GL (Fin 2) (Qbar l)), AttC ι r π → ImaginaryQuadraticEtaCharacter.AllWin π →
    Z.InvariantSubmoduleMonicPolynomial.E.SplitBad K π → ∀ R : G K Ω →* GL (Fin 4) (Qbar l), Z.Bc.IndCh (galEmb K M Ω) r R → AllW ι R

end UpperTheory.V.Z.Win.Birth
end
end

