module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0038
public import Formalism.LocalToGlobal.Columns.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElevenLeInertOddPrimeImagQuadraticLargeScale
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeEleven

theorem eleven_le : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (l : ℕ),
    L.sc.ez = eps → x0 ≤ L.sc.x → l.Prime → InertUnr D l → 11 ≤ l := by
  intro eps heps
  refine ⟨(11 : ℝ) ^ (5 / eps), ?_⟩
  intro D L l he hx hl hin
  have hlt := GlobalTheory.InertPrimeLarge.lt_prime L l hl hin.ne_two hin.2.2.2
  rw [he] at hlt
  have h0 : (0 : ℝ) ≤ (11 : ℝ) ^ (5 / eps) := Real.rpow_nonneg (by norm_num) _
  have hmono : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) ≤ L.sc.x ^ (eps / 5) :=
    Real.rpow_le_rpow h0 hx (by positivity)
  have h11 : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) = 11 := by
    rw [← Real.rpow_mul (by norm_num)]
    have : 5 / eps * (eps / 5) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have : (11 : ℝ) < l := by linarith
  exact_mod_cast this.le

end GlobalTheory.InertPrimeEleven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseReads
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem exists_base_reads : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (ι : Om l ≃+* ℂ) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g₀ : R.GG), ι.toRingHom.comp (LL.1.val.toRingHom.comp (τ₀.toRingHom.comp c)) = H.emb g₀ → ∃ κ : H.E →+* ↥LL.1, ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g : R.GG), ι.toRingHom.comp (LL.1.val.toRingHom.comp (τ.toRingHom.comp c)) = H.emb g → Reads H c κ τ g := by
  intro R H l _ K LL c ι τ₀ g₀ h₀
  refine ⟨τ₀.toRingHom.comp (c.comp ((H.sigmaOf g₀).symm : H.E →+* H.E)), ?_⟩
  intro τ g hτ x
  have hinj : Function.Injective (fun y : ↥LL.1 => ι (LL.1.val y)) :=
    ι.injective.comp (LL.1.val.injective)
  apply hinj
  have e1 := DFunLike.congr_fun hτ x
  have e2 := DFunLike.congr_fun h₀ ((H.sigmaOf g₀).symm (H.sigmaOf g x))
  simp only [RingHom.comp_apply] at e1 e2
  simp only [RingHom.comp_apply]
  change ι (LL.1.val (τ (c x))) = ι (LL.1.val (τ₀ (c ((H.sigmaOf g₀).symm (H.sigmaOf g x)))))
  have e1' : ι (LL.1.val (τ (c x))) = H.emb g x := e1
  have e2' : ι (LL.1.val (τ₀ (c ((H.sigmaOf g₀).symm (H.sigmaOf g x))))) = H.emb g₀ ((H.sigmaOf g₀).symm (H.sigmaOf g x)) := e2
  rw [e1', e2']
  simp [Host.emb]

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDecorationExtensionAtPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.FrameDeco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}


omit [StarRing E] in
theorem exists_inv_mod (P : HeightOneSpectrum (𝓞 E)) {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    ∃ a p : 𝓞 E, p ∈ P.asIdeal ∧ a * s + p = 1 := by
  obtain ⟨a, p, hp, h⟩ := P.isMaximal.exists_inv hs
  exact ⟨a, p, hp, h⟩

theorem smul_localizationAt_le (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) :
    P.asIdeal • localization₂ P.asIdeal N ≤ localization₂ P.asIdeal (P.asIdeal • N) := by
  rw [Submodule.smul_le]
  intro r hr x hx
  obtain ⟨t, ht, htx⟩ := (mem_locP P N x).1 hx
  refine (mem_locP P _ _).2 ⟨t, ht, ?_⟩
  rw [smul_comm]
  exact Submodule.smul_mem_smul hr htx

theorem mem_smul_of_mem_locP (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    {y : Sp E n} (hy : y ∈ N) (h : y ∈ localization₂ P.asIdeal (P.asIdeal • N)) : y ∈ P.asIdeal • N := by
  obtain ⟨t, ht, hty⟩ := (mem_locP P _ _).1 h
  obtain ⟨a, p, hp, e⟩ := exists_inv_mod P ht
  have : y = a • (t • y) + p • y := by
    rw [smul_smul, ← add_smul, e, one_smul]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hty) (Submodule.smul_mem_smul hp hy)

theorem redV_add (P : HeightOneSpectrum (𝓞 E)) {x y : Sp E n}
    (hx : x ∈ stdAt E n P) (hy : y ∈ stdAt E n P) : redV P (x + y) = redV P x + redV P y := by
  funext i
  exact reduction_add ((mem_localization_standardLattice _ _).1 hx _) ((mem_localization_standardLattice _ _).1 hy _)

theorem redV_osmul (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) {x : Sp E n}
    (hx : x ∈ stdAt E n P) :
    redV P (a • x) = Ideal.Quotient.mk P.asIdeal a • redV P x := by
  funext i
  exact redP_osmul a ((mem_localization_standardLattice _ _).1 hx _)

theorem exists_deco_of_frames : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := ∅)) (f : SG → (Sp E n ≃ₗ[E] Sp E n)), (∀ (w : SG) (x : Sp E n), f w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) → ∃ d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), d'.1.N = d.1.N ∧ d'.1.f = d.1.f ∧ ∀ w : SG, ∀ x ∈ stdAt E n w.1, d'.1.be w (f w x) = redV w.1 x := by
  classical
  intro E _ _ _ n ST SG d f hf
  have hf' : ∀ (w : SG) (y : Sp E n), y ∈ d.1.at w.1 → (f w).symm y ∈ stdAt E n w.1 := by
    intro w y hy
    exact (hf w _).1 (by simpa using hy)
  let D : Deco E n ST SG :=
    { N := d.1.N
      f := d.1.f
      be := fun w y => if y ∈ d.1.at w.1 then redV w.1 ((f w).symm y) else 0 }
  have hbe : ∀ (w : SG) (y : Sp E n), y ∈ d.1.at w.1 → D.be w y = redV w.1 ((f w).symm y) :=
    fun w y hy => if_pos hy
  have hsm : ∀ (w : SG) (a : 𝓞 E), ∀ x ∈ d.1.at w.1,
      D.be w (a • x) = Ideal.Quotient.mk w.1.asIdeal a • D.be w x := by
    intro w a x hx
    rw [hbe w _ (Submodule.smul_mem _ a hx), hbe w _ hx, equiv_osmul, redV_osmul _ _ (hf' w x hx)]
  have hD : D.Ok :=
    { lat := d.2.lat
      uni := d.2.uni
      f_add := d.2.f_add
      f_smul := d.2.f_smul
      f_off := d.2.f_off
      f_ne := d.2.f_ne
      be_add := by
        intro w x hx y hy
        replace hx : x ∈ d.1.at w.1 := hx
        replace hy : y ∈ d.1.at w.1 := hy
        rw [hbe w _ (Submodule.add_mem _ hx hy), hbe w _ hx, hbe w _ hy, map_add (f := _),
          redV_add _ (hf' w x hx) (hf' w y hy)]
      be_smul := hsm
      be_off := fun w x hx => if_neg hx
      be_surj := by
        intro w c
        choose r hr using fun i => Ideal.Quotient.mk_surjective (c i)
        have h1 : (fun i => algebraMap (𝓞 E) E (r i) : Sp E n) ∈ stdLat E n :=
          (mem_stdLat _).2 fun i => ⟨r i, rfl⟩
        have h2 := (hf w _).2 (le_locP _ _ h1)
        obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 h2
        obtain ⟨a, p, hp, e⟩ := exists_inv_mod w.1 hs
        refine ⟨a • s • _, Submodule.smul_mem _ a hsy, ?_⟩
        have e' : Ideal.Quotient.mk w.1.asIdeal (a * s) = 1 := by
          have := congrArg (Ideal.Quotient.mk w.1.asIdeal) e
          rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero, map_one] at this
        rw [smul_smul, hsm w _ _ h2, e', one_smul, hbe w _ h2, LinearEquiv.symm_apply_apply]
        funext i
        exact (reduction_coe _ _).trans (hr i)
      be_ker := by
        intro w y hy h0
        replace hy : y ∈ d.1.N := hy
        have hy' : y ∈ d.1.at w.1 := le_locP _ _ hy
        rw [hbe w _ hy'] at h0
        have hx := hf' w y hy'
        obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx
        have h0' : redV w.1 (s • (f w).symm y) = 0 := by
          rw [redV_osmul _ _ hx, h0, smul_zero]
        choose r hr using (mem_stdLat _).1 hsx
        have hmem : ∀ i, r i ∈ w.1.asIdeal := by
          intro i
          have h3 : redP w.1 ((s • (f w).symm y) i) = 0 := congrFun h0' i
          rw [← hr i, reduction_coe] at h3
          exact Ideal.Quotient.eq_zero_iff_mem.1 h3
        have h4 : s • (f w).symm y
            = ∑ i, r i • (Pi.single i (algebraMap (𝓞 E) E 1) : Sp E n) := by
          generalize s • (f w).symm y = x at hr
          funext j
          simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
        have h5 : s • y ∈ w.1.asIdeal • d.1.at w.1 := by
          have : s • y = f w (s • (f w).symm y) := by
            rw [equiv_osmul, LinearEquiv.apply_symm_apply]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [this, h4, map_sum]
          refine Submodule.sum_mem _ fun i _ => ?_
          rw [equiv_osmul]
          exact Submodule.smul_mem_smul (hmem i)
            ((hf w _).2 (le_locP _ _ (single_mem_stdLat i 1)))
        obtain ⟨t, ht, hts⟩ := (mem_locP _ _ _).1 (smul_localizationAt_le w.1 d.1.N h5)
        refine mem_smul_of_mem_locP w.1 d.1.N hy ((mem_locP _ _ _).2 ⟨t * s, ?_, ?_⟩)
        · exact fun hm => (w.1.isPrime.mem_or_mem hm).elim ht hs
        · rwa [mul_smul] }
  refine ⟨⟨D, hD⟩, rfl, rfl, fun w x hx => ?_⟩
  change D.be w (f w x) = _
  rw [hbe w _ ((hf w x).2 hx), LinearEquiv.symm_apply_apply]

end GlobalTheory.FrameDeco
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFactorStrictHenselisation
section
open IsLocalRing

namespace GlobalTheory.StrictHensFactor

theorem exists_factor_strictHenselisation : ∀ (A C B : Type) [CommRing A] [IsLocalRing A] [CommRing C] [Algebra A C] [CommRing B] [HenselianLocalRing B] [IsSepClosed (ResidueField B)] [Algebra A B] [IsLocalHom (algebraMap A B)] (u : C →ₐ[A] B), ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : Algebra A D) (c : C →ₐ[A] D) (w : D →ₐ[A] B), w.comp c = u ∧ ∃ (P : Ideal C) (_ : P.IsPrime) (φ : Localization.AtPrime P →+* D), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ ∧ φ.comp (algebraMap C (Localization.AtPrime P)) = (c : C →+* D) ∧ P.comap (algebraMap A C) = maximalIdeal A := by
  intro A C B _ _ _ _ _ _ _ _ _ u
  set P : Ideal C := (maximalIdeal B).comap (u : C →+* B) with hP
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime P
  have hu : ∀ y : P.primeCompl, IsUnit ((u : C →+* B) y) := by
    intro y
    have := y.2
    by_contra hy
    exact this ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let b : L →+* B := IsLocalization.lift hu
  have hb : b.comp (algebraMap C L) = (u : C →+* B) := IsLocalization.lift_comp hu
  haveI hbloc : IsLocalHom b := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro ha
    have h1 : (u : C →+* B) a = (u : C →+* B) s * b (IsLocalization.mk' _ a s) :=
      (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
    have h2 : IsUnit ((u : C →+* B) a) := by
      rw [h1]; exact (hu s).mul hx
    exact (IsLocalRing.mem_maximalIdeal _).1 ha h2
  obtain ⟨S, _, _, _, hloc, hsc, -, -, -, ι, _, _, _, Si, hmono, hcov, hA⟩ :=
    GlobalTheory.exists_strictHenselisation L (SeparableClosure (ResidueField L))
  have hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap L S) := by
    refine GlobalTheory.StrictHensUnion.indEtale_of_directed_union L S ι Si hmono hcov fun i => ?_
    obtain ⟨A', _, _, _, q, _, ⟨e⟩⟩ := hA i
    exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
      (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale L A' q.primeCompl)
  have hstrict : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation (algebraMap L S) :=
    ⟨inferInstance, hsc, hloc, hind⟩
  obtain ⟨g, hg⟩ := GlobalTheory.NCyc.StrictLocLift.exists_ringHom_of_isStrictHenselisation
    (algebraMap L S) hstrict b
  let cR : C →+* S := (algebraMap L S).comp (algebraMap C L)
  letI algAS : Algebra A S := (cR.comp (algebraMap A C)).toAlgebra
  let c : C →ₐ[A] S := { cR with commutes' := fun a => rfl }
  have hgc : g.comp cR = (u : C →+* B) := by
    rw [← RingHom.comp_assoc, hg, hb]
  let w : S →ₐ[A] B :=
    { g with
      commutes' := fun a => by
        change g (cR (algebraMap A C a)) = algebraMap A B a
        rw [← RingHom.comp_apply, hgc]
        exact u.commutes a }
  refine ⟨S, inferInstance, inferInstance, algAS, c, w, ?_, P, hPp, algebraMap L S, hstrict, rfl, ?_⟩
  · ext x
    exact DFunLike.congr_fun hgc x
  · ext a
    rw [hP, Ideal.comap_comap, Ideal.mem_comap]
    have : ((u : C →+* B).comp (algebraMap A C)) a = algebraMap A B a := u.commutes a
    rw [this, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]

end GlobalTheory.StrictHensFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FramedForms

section Torsor

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem deco_smul (a : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) (p : DecoF E n ST SG Q) :
    (a • p).deco = (a.1, a.2.1) • p.deco := rfl

theorem fr_smul (a : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) (p : DecoF E n ST SG Q) (P : Q) :
    (a • p).fr P = a.1.1 * p.fr P * ((a.2.2 P)⁻¹).1 := rfl

theorem exists_smul_of_deco_eq {p q : DecoF E n ST SG Q} (h : p.deco = q.deco) :
    ∃ c : GLQ E n Q, q = ((1, 1, c) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p := by
  have h' : p.1.1 = q.1.1 := h
  refine ⟨fun P => ⟨(q.fr P)⁻¹ * p.fr P, fun x => ?_⟩, ?_⟩
  · have h1 := q.2 P (((q.fr P)⁻¹ * p.fr P) x)
    have h2 : q.1.2 P (((q.fr P)⁻¹ * p.fr P) x) = p.1.2 P x :=
      LinearEquiv.apply_symm_apply (q.1.2 P) (p.1.2 P x)
    rw [h2, ← h'] at h1
    exact h1.symm.trans (p.2 P x)
  · apply Subtype.ext
    apply Prod.ext
    · exact h'.symm.trans (one_smul (UF E n × GLG (E := E) (n := n) (SG := SG)) p.1.1).symm
    · funext P
      show q.fr P = (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((q.fr P)⁻¹ * p.fr P)⁻¹
      group

theorem stab_inj (p : DecoF E n ST SG Q) {a b : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q}
    (ha : a • p = p) (hb : b • p = p) (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1) : a = b := by
  refine Prod.ext h1 (Prod.ext h2 ?_)
  funext P
  have e1 : (a • p).fr P = (b • p).fr P := by rw [ha, hb]
  rw [fr_smul, fr_smul, h1] at e1
  exact inv_injective (Subtype.ext (mul_left_cancel e1))

end Torsor

section Form

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem incl_injective (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) :
    Function.Injective (FrmG.incl Λ Θ) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun x => x.2.1) h
  have h3 := congrArg (fun x => x.2.2) h
  exact Prod.ext h1 (Prod.ext (Subtype.ext h2) (Subtype.ext h3))

theorem grp_finiteIndex (Θ : LevQFam X.E X.K n Q) (h : ∀ R : Q, (Θ R).H.FiniteIndex) :
    Θ.grp.FiniteIndex := by
  have h1 : ∀ R : Q, ((Θ R).H.comap (Pi.evalMonoidHom (fun P : Q => ↥(GLint X.E n P.1)) R)).FiniteIndex := by
    intro R
    refine ⟨?_⟩
    rw [Subgroup.index_comap_of_surjective _ (Function.surjective_eval R)]
    exact (h R).index_ne_zero
  have h2 := Subgroup.finiteIndex_iInf h1
  refine Subgroup.finiteIndex_of_le (H := ⨅ R : Q, (Θ R).H.comap
    (Pi.evalMonoidHom (fun P : Q => ↥(GLint X.E n P.1)) R)) ?_
  intro c hc
  exact (Subgroup.mem_pi _).mpr fun R _ => Subgroup.mem_iInf.mp hc R

theorem chr_root (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)
    (hΘ : ∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) ^ m = 1 := by
  obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2.1
  obtain ⟨k, hk, hk'⟩ := hΘ g.2.2
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  have hk2 : ((Θ.chr g.2.2 : X.Kˣ) : X.K) ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hk', Units.val_one]
  rw [Units.val_mul, mul_pow, pow_mul, hc, one_pow, one_mul, mul_comm m k, pow_mul, hk2, one_pow]

theorem frmGSD_ok (hX : X.Ok) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (hC : C.Eqv)
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (hfi : ∀ R : Q, (Θ R).H.FiniteIndex)
    (hΘ : ∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) :
    (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ).Ok := by
  refine { fin_orb := ?_, fin_stab := ?_, nab_smul := ?_, del_smul := ?_, inv := ?_ }
  · obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have := grp_finiteIndex Θ hfi
    let T : Set (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) := {d | d ∈ s ∧ ∃ p : DecoF X.E n ST SG Q, p.deco = d}
    have hT : Finite T := hs.subset fun d hd => hd.1
    let S := frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ
    refine Finite.of_surjective (fun x : T × (GLQ X.E n Q ⧸ Θ.grp) =>
      S.cls (((1, 1, (x.2.out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • x.1.2.2.choose)) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)
      have hq : (((g⁻¹, 1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • (p : DecoF X.E n ST SG Q)).deco = d0 := by
        rw [deco_smul, hg, smul_smul]
        simp only [Prod.mk_mul_mk, inv_mul_cancel, mul_one]
        exact one_smul (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) d0
      have hd : d0 ∈ T := ⟨hd0, _, hq⟩
      obtain ⟨c, hc⟩ := exists_smul_of_deco_eq (hd.2.choose_spec.trans hq.symm)
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Θ.grp c⁻¹
      refine ⟨(⟨d0, hd⟩, (c⁻¹ : GLQ X.E n Q)), ?_⟩
      refine (S.cls_eq_iff _ p).mpr ⟨((g⁻¹, 1, h⁻¹) : FrmG Λ Θ), ?_⟩
      show ((g⁻¹, 1, (h : GLQ X.E n Q)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • (p : DecoF X.E n ST SG Q) =
        ((1, 1, ((c⁻¹ : GLQ X.E n Q) : GLQ X.E n Q ⧸ Θ.grp).out⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) •
          hd.2.choose
      have e1 : ((g⁻¹, 1, (h : GLQ X.E n Q)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) =
          (1, 1, (h : GLQ X.E n Q)⁻¹) * (g⁻¹, 1, 1) := by simp
      rw [e1, mul_smul, hc, smul_smul, hh]
      simp
  · intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p)
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ).G p =>
        (⟨((FrmG.incl Λ Θ a.1).1, (FrmG.incl Λ Θ a.1).2.1), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (DecoF.deco p))) ?_
    intro a b hab
    have h0 := congrArg Subtype.val hab
    exact Subtype.ext (incl_injective Λ Θ
      (stab_inj p a.2 b.2 (Prod.mk.inj h0).1 (Prod.mk.inj h0).2))
  · intro g p
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    exact (hC.nab_smul ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1) (DecoF.deco p)).trans
      (map_root_smul _ _ hm hc).symm
  · intro g p
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    exact (hC.del_smul ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1) (DecoF.deco p)).trans
      (map_root_smul _ _ hm hc).symm
  · intro g x y
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    show C.pair (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • C.rho g.1 x)
      (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv g.1 x y, smul_smul]
    show (star ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

theorem main : ∀ {X : Fields} (_ : X.Ok) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (lam : X.Tau → DomWeight n) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q),
    (∀ R : Q, (Θ R).H.FiniteIndex) → (∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) →
    (frmGSD ((roundPk X lam fun d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) => d.1.Lsh).pull DecoF.deco) Λ Θ).Ok := by
  intro X hX n ST SG Q lam Λ Θ h1 h2
  exact frmGSD_ok hX _
    ⟨fun a d => roundPk_nab X _ _ (d.1.Lsh_act a.1.2 a.2), fun a d => roundPk_del X _ _ (d.1.Lsh_act a.1.2 a.2),
      roundPk_inv X _ _ hX.emb_star⟩ Λ Θ h1 h2

end Form

end GlobalTheory.FramedForms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem existsUnique_reads : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (κ : H.E →+* ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), ∃! g : R.GG, Reads H c κ τ g := by
  intro R H l _ K LL c κ τ
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  obtain ⟨σ, hσ⟩ := GlobalTheory.HTW.exists_aut_comp_eq_of_normal κ ((τ : ↥K.1 →+* ↥LL.1).comp c)
  obtain ⟨g, hg⟩ := (H.gal).symm.surjective σ
  have hg' : H.sigmaOf g = σ := hg
  refine ⟨g, fun x => ?_, fun g' hg2 => ?_⟩
  · rw [hg']
    exact hσ x
  · have e : H.sigmaOf g' = H.sigmaOf g := by
      refine AlgEquiv.ext fun x => ?_
      apply κ.injective
      rw [← hg2 x, hg']
      exact hσ x
    exact (H.gal).symm.injective e

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem goodO_finExt_integers :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  GlobalTheory.Pass.goodO_ringOfIntegers

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSmallBoundsLeParametersRoundedSizeBoundStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_smallBounds_le_roundedSizeBound : ∀ {D : D7} (L : SizeData₂ D) (C C' : ℝ) (j : ℕ), Roomy L C' → 0 ≤ C → 2 * C ≤ C' → 2 * j + 2 ≤ D.host.Lw → C * ((j : ℝ) + 1) * (((wHat D + sHat L + etaHat L : ℕ) : ℝ) + 1) ≤ (bHat L : ℝ) := by
  first | exact @GlobalTheory.HTW.mul_small_le_bHat | exact GlobalTheory.HTW.mul_small_le_bHat | (intros; apply GlobalTheory.HTW.mul_small_le_bHat <;> assumption)
end

