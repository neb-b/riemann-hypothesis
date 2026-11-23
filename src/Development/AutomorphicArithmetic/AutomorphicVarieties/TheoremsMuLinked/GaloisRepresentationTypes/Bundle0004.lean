module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.MatrixIrreducibility.IrrOfMatIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.DerAdjoin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapRingHomSingleMulPartialCharpoly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ArPl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CharpolyPowTwoByTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem irr2 {G κ k A : Type} [Group G] [Field κ] [IsAlgClosed κ] [Field k] [CommRing A]
    (r : G →* GL (Fin 2) κ) (hr : U3.MatIrr ⊤ (Pr.gm r)) (j : A →+* κ) (hj : Function.Injective j) (φ : A →+* k)
    (χ : G →* kˣ) (t : G → A) (ht : ∀ g, j (t g) = (Pr.gm r g).trace)
    (hχ : ∀ g, φ (t g) = (χ g : kˣ) + ((χ g)⁻¹ : kˣ)) (U : Subgroup G) [U.Normal] {u : G} (hu : u ∈ U)
    (hd : (Pr.gm r u).det = 1) (hne : χ u ^ 2 ≠ 1) : U3.MatIrr U (Pr.gm r) := by
  have hy : ((χ u : kˣ) : k) ^ 2 - 1 ≠ 0 := fun h => hne (Units.ext (by simpa [sub_eq_zero] using h))
  rcases Pr.cliffPrime G κ 2 Nat.prime_two r hr U with h | h | ⟨b, la, π, -, hla, hπ, htr⟩
  · exact h
  · exfalso
    obtain ⟨a, ha⟩ := h u hu
    have e : t u ^ 2 = 4 := by
      apply hj
      rw [map_pow, ht, map_ofNat]
      rw [ha] at hd ⊢
      simp only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at hd ⊢
      push_cast
      linear_combination 4 * hd
    have e2 := congrArg φ e
    rw [map_pow, hχ, map_ofNat] at e2
    have e3 := (χ u).mul_inv
    apply pow_ne_zero 2 hy
    linear_combination ((χ u : kˣ) : k) ^ 2 * e2 - (2 * ((χ u : kˣ) : k) ^ 2 + (χ u : kˣ) * ((χ u)⁻¹ : kˣ) + 1) * e3
  · exfalso
    obtain ⟨g, hg⟩ := htr 0 1
    have hne' : ∀ i, π g i ≠ i := by
      intro i hi
      fin_cases i
      · exact absurd (hg.symm.trans hi) (by decide)
      · exact absurd ((π g).injective (hg.trans hi.symm)) (by decide)
    have tr0 : ∀ s ∈ U, (Pr.gm r (g * s)).trace = 0 := fun s hs => by
      rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_matrix_trace κ b]
      refine Finset.sum_eq_zero fun i _ => ?_
      obtain ⟨a, ha⟩ := hπ g i
      have := hla i ⟨s, hs⟩
      simp only [Pr.gm] at this ha
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Matrix.toLin'_apply]
      simp only [Pr.gm, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      rw [this, Matrix.mulVec_smul, ha]
      simp [hne' i]
    have z : ∀ s ∈ U, ((χ (g * s) : kˣ) : k) ^ 2 + 1 = 0 := fun s hs => by
      have e : t (g * s) = 0 := hj (by rw [ht, tr0 s hs, map_zero])
      have e2 := hχ (g * s)
      rw [e, map_zero] at e2
      have e3 := (χ (g * s)).mul_inv
      linear_combination -((χ (g * s) : kˣ) : k) * e2 - e3
    have z1 := z 1 U.one_mem
    have z2 := z u hu
    rw [mul_one] at z1
    rw [map_mul, Units.val_mul] at z2
    apply hy
    linear_combination ((χ u : kˣ) : k) ^ 2 * z1 - z2

private theorem pair2 {κ : Type} [Field κ] :
    ∃ J : GL (Fin 2) κ, ∀ M : Matrix (Fin 2) (Fin 2) κ, M.transpose * J.val * M = M.det • J.val := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun M => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem freeRes {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (L : Type) [Field L]
    [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (h : FreeAt l W) :
    FreeAt l (W.comp (Base.galEmb ℚ L Ω)) :=
  _root_.UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.freeRes L W h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapOfRep
section
open UpperTheory.V UpperTheory.V.Th

namespace UpperTheory.V.Th.NormTraceLemmas

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : HV.Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm

private theorem locP_of (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) : Pa.LocP :=
  ⟨GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.loc.llc P.loc.conv P.loc.dzc P.loc.dzi P.loc.brauer P.loc.chev P.aut.art
               P.loc.exh P.loc.multi P.loc.cos P.loc.zel P.loc.geo P.loc.bz,
    P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2

private theorem unip_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (hM : (M.map (residue O)).charpoly = (Polynomial.X - 1) ^ n) (i j : Fin n) :
    (M ^ l ^ (n + m) - 1) i j ∈ maximalIdeal O ^ m := by
  have hl : l.Prime := Fact.out
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h0 := Matrix.aeval_self_charpoly (M.map (residue O))
  rw [hM] at h0
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one] at h0
  have h1 : (residue O).mapMatrix (M ^ l ^ n) = 1 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self hl.one_lt (n := n)).le
    have h4 := sub_pow_char_pow_of_commute l n (Commute.one_right (M.map (residue O)))
    rw [one_pow] at h4
    rw [map_pow, ← sub_eq_zero]
    refine h4.symm.trans ?_
    rw [hd, pow_add, h0, zero_mul]
  have h2 : ∀ k, (residue O).mapMatrix (M ^ l ^ (n + k)) = 1 := fun k => by
    rw [pow_add, pow_mul, map_pow, h1, one_pow]
  induction m generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pow_succ l, pow_mul, ← mul_geom_sum, Matrix.mul_apply, pow_succ]
    refine Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih i a) ?_
    have h3 : (residue O).mapMatrix (∑ t ∈ Finset.range l, (M ^ l ^ (n + k)) ^ t) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_pow (residue O).mapMatrix (M ^ l ^ (n + k)), h2, one_pow]
      simp
    exact (residue_eq_zero_iff _).1 (congrFun (congrFun h3 a) j)

private theorem rhoPLO (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CharP (ResidueField O) l] (n : ℕ) (ρ : F.G₀ →* GL (Fin n) O)
    (hc : ∀ i j, AdicCont (maximalIdeal O) fun g => mat ρ g i j) (H : OpenNormalSubgroup F.Γ)
    (hH : ∀ g ∈ H, ∃ h : F.η g = 1, ((mat ρ ⟨g, h⟩).map (residue O)).charpoly = (Polynomial.X - 1) ^ n)
    (g : F.G₀) (hg : (g : F.Γ) ∈ PL l H.toSubgroup) : ρ g = 1 := by
  have key : ∀ (m : ℕ) (i j : Fin n), (mat ρ g - 1) i j ∈ maximalIdeal O ^ m := by
    intro m
    let π := Ideal.Quotient.mk (maximalIdeal O ^ m)
    let Km : Subgroup F.G₀ := (π.mapMatrix.toMonoidHom.comp (mat ρ)).toHomUnits.ker
    have hKm : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j) := by
      intro a
      rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one, ← map_one π.mapMatrix,
        ← Matrix.ext_iff]
      rfl
    have hKm' : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, (mat ρ a - 1) i j ∈ maximalIdeal O ^ m := by
      intro a
      simp only [hKm, Matrix.sub_apply, π, Ideal.Quotient.eq]
    have ho : IsOpen (Km : Set F.G₀) := by
      have : (Km : Set F.G₀) = ⋂ i, ⋂ j, {a | π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j)} := by
        ext a
        simp only [SetLike.mem_coe, hKm, Set.mem_iInter, Set.mem_setOf_eq]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hc i j m).isOpen_fiber _
    let K' : Subgroup F.Γ := Km.map F.η.ker.subtype
    have ho' : IsOpen (K' : Set F.Γ) := F.η_open.isOpenMap_subtype_val _ ho
    haveI : Finite (F.Γ ⧸ K') := Subgroup.quotient_finite_of_isOpen K' ho'
    haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hc : IsOpen (K'.normalCore : Set F.Γ) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K'.normalCore_isClosed (K'.isClosed_of_isOpen ho'))
    let U : OpenNormalSubgroup F.Γ := ⟨⟨K'.normalCore, hc⟩, K'.normalCore_normal⟩
    have hU : ∀ h ∈ H.toSubgroup, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨n + m, fun b => ?_⟩
      obtain ⟨h1, h2⟩ := hH (b * h * b⁻¹) (H.isNormal'.conj_mem h hh b)
      refine ⟨(⟨b * h * b⁻¹, h1⟩ : F.G₀) ^ l ^ (n + m), ?_, ?_⟩
      · rw [SetLike.mem_coe, hKm', map_pow]
        exact unip_pow l O n m _ h2
      · simp only [Subgroup.coe_subtype, SubgroupClass.coe_pow, conj_pow]
    have h3 : (g : F.Γ) ∈ K'.normalCore := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg U) hU
    obtain ⟨a, ha, hag⟩ := K'.normalCore_le h3
    obtain rfl : a = g := Subtype.ext hag
    exact (hKm' a).1 ha
  apply Units.ext
  ext1 i j
  have h0 : (mat ρ g - 1) i j ∈ (⨅ m : ℕ, maximalIdeal O ^ m) := Ideal.mem_iInf.2 fun m => key m i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot, Matrix.sub_apply,
    sub_eq_zero] at h0
  exact h0

private theorem red_unip {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B]
    [IsCO O B] (u : Pair r B) (x : B →ₐ[O] O) (ρ : F.G₀ →* GL (Fin n) O) (h : u.D.map x.toRingHom = GDet.ofRep (mat ρ))
    (g : F.G₀) (hg : ∀ i, r.chib i g = 1) : ((mat ρ g).map (residue O)).charpoly = (Polynomial.X - 1) ^ n := by
  have e0 : (residue O).comp x.toRingHom = (res O B : B →+* ResidueField O) := RingHom.ext fun a =>
    ((res O O).commutes (x a)).symm.trans (res_map x a)
  have e3 : (GDet.ofRep (mat ρ)).map (residue O) = r.Dbar := by
    rw [← h, ← u.red, ← e0]
    rfl
  rw [map_ofRep, Resid.Dbar] at e3
  have e4 := congrArg (·.chi (MonoidAlgebra.single g 1)) e3
  simp only [chi_ofRep] at e4
  refine e4.trans ?_
  have e5 : W.diagRep r.chib g = 1 := by
    change Matrix.diagonal _ = _
    simp only [hg, Units.val_one, Matrix.diagonal_one]
  rw [e5, Matrix.charpoly_one, Fintype.card_fin]

end UpperTheory.V.Th.NormTraceLemmas

open UpperTheory.V.Th.NormTraceLemmas UpperTheory.V.Pa UpperTheory.V.W UpperTheory.V.Alg in
theorem UpperTheory.V.Th.coreO :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → CoreO := by
  intro hN l _ L Ω _ _ _ _ _ _ s V0 c n r B J y x h q sg al hS hn hLev hJ hAr hmap hN4 hsg hdet δ hδ h0
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  haveI := coef_isCoef l c
  haveI := IsCoef.char (l := l) (O := c.O)
  haveI := IsCoef.finite (l := l) (O := c.O)
  haveI := IsCoef.complete (l := l) (O := c.O)
  obtain ⟨b, hb, hγ, hctrl⟩ := hLev
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := (arPl hC l L Ω s V0 c.O n r hS).2 q sg fun j => (hsg j).1
  obtain rfl : T.sg = sg := funext hTs
  have hI := (ipEq l L Ω s V0 c.O n r).1
  have hgen : GenBy c.O (pairVals (pairOf B.u)) := fun N b => by
    obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
    refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
    rintro _ (⟨a, g, -, -, rfl⟩ | e)
    · exact Or.inl ⟨a, g, rfl⟩
    · exact Or.inr e
  have hmap' : (pairOf B.u).Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ := hmap
  have hker : ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1 := by
    refine rhoPLO l (globOf r V0).frame c.O n y.ρ y.cont T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    exact ⟨e1, red_unip (pairOf B.u) x y.ρ hmap'.1 ⟨g, e1⟩ e2⟩
  have heig : Eig y T al := fun j => (hsg j).2
  exact count l _ (globOf r V0) T n c.O (residOf r) B.B (pairOf B.u) J _ b y x al s.odd hn
    ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
    (hasOp (locP_of hN) l L Ω s V0 c.O n r B J _ b hb T Pl) hgen hmap' hJ
    (etOf l _ (globOf r V0) n c.O (residOf r) B.B (pairOf B.u) J _ b y x hn hmap' hgen (hctrl x h hAr)) hker heig
    (b1O hC l L Ω s V0 c n r T Pl y al hS (W.locCFT hN.aut.art hC l L Ω s) hn hker hN4 heig hdet)
    δ hδ fun k => h0 _ _ _ (hγ k)
end

